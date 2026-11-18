/*
 * lstz.cpp - Plugin WCX (Packer) para Total Commander: catálogos comprimidos .lstz
 *
 * Formato del archivo (little-endian):
 *   [0..5]   "LSTZ01"
 *   [6..7]   uint16 reservado (0)
 *   [8..15]  uint64 tamaño del índice descomprimido
 *   [16..23] uint64 tamaño del bloque comprimido
 *   [24..27] uint32 CRC32 del índice descomprimido
 *   [28..]   índice comprimido (zlib/DEFLATE, vía miniz)
 *
 * Índice descomprimido (UTF-8), una línea por entrada:
 *   RutaRelativa \t Tamaño \t FechaUnix(UTC) \t AtributosWin32 \n
 */

#define _CRT_SECURE_NO_WARNINGS
#include <windows.h>
#include <string>
#include <vector>
#include <map>
#include <new>
#include <utility>
#include <string.h>

#include "wcxhead.h"
#include "miniz.h"

#define WCX_API(ret) extern "C" __declspec(dllexport) ret __stdcall

namespace {

const char   kMagic[6]  = { 'L', 'S', 'T', 'Z', '0', '1' };
const size_t kHdrSize   = 28;
const unsigned long long kMaxIndex = 0x70000000ULL;   // límite de seguridad (~1,75 GB)

struct Entry {
    unsigned long long size;
    long long          unixTime;
    DWORD              attr;
    Entry() : size(0), unixTime(0), attr(0) {}
};

struct Item {
    std::wstring name;
    Entry        e;
};

struct Archive {
    std::vector<Item> items;
    size_t            pos;     // próxima entrada a entregar / procesar
    Archive() : pos(0) {}
};

typedef std::map<std::wstring, Entry> EntryMap;

tProcessDataProc  g_procA = NULL;
tProcessDataProcW g_procW = NULL;
unsigned          g_tick  = 0;

/* ---------- Conversiones de texto ---------- */

std::wstring FromUtf8(const char* p, size_t len) {
    if (!len) return std::wstring();
    int n = MultiByteToWideChar(CP_UTF8, 0, p, (int)len, NULL, 0);
    std::wstring w((size_t)n, L'\0');
    MultiByteToWideChar(CP_UTF8, 0, p, (int)len, &w[0], n);
    return w;
}

std::string ToUtf8(const std::wstring& w) {
    if (w.empty()) return std::string();
    int n = WideCharToMultiByte(CP_UTF8, 0, w.data(), (int)w.size(), NULL, 0, NULL, NULL);
    std::string s((size_t)n, '\0');
    WideCharToMultiByte(CP_UTF8, 0, w.data(), (int)w.size(), &s[0], n, NULL, NULL);
    return s;
}

std::wstring FromAnsi(const char* s) {
    if (!s || !*s) return std::wstring();
    int len = (int)strlen(s);
    int n = MultiByteToWideChar(CP_ACP, 0, s, len, NULL, 0);
    std::wstring w((size_t)n, L'\0');
    MultiByteToWideChar(CP_ACP, 0, s, len, &w[0], n);
    return w;
}

bool ToAnsi(const std::wstring& w, char* out, int cap) {
    return WideCharToMultiByte(CP_ACP, 0, w.c_str(), -1, out, cap, NULL, NULL) > 0;
}

/* Prefijo \\?\ para rutas largas (>= 240 caracteres) */
std::wstring LongPath(const std::wstring& p) {
    if (p.size() < 240 || p.compare(0, 4, L"\\\\?\\") == 0) return p;
    if (p.compare(0, 2, L"\\\\") == 0) return L"\\\\?\\UNC\\" + p.substr(2);
    return L"\\\\?\\" + p;
}

/* ---------- Números sin depender de printf/strtoll (evita diferencias msvcrt/UCRT) ---------- */

void AppendU64(std::string& s, unsigned long long v) {
    char b[24];
    int i = 24;
    do { b[--i] = (char)('0' + (int)(v % 10)); v /= 10; } while (v);
    s.append(b + i, (size_t)(24 - i));
}

void AppendI64(std::string& s, long long v) {
    if (v < 0) { s += '-'; AppendU64(s, 0ULL - (unsigned long long)v); }
    else AppendU64(s, (unsigned long long)v);
}

unsigned long long ParseU64(const char* p, const char* e) {
    unsigned long long v = 0;
    for (; p < e && *p >= '0' && *p <= '9'; ++p) v = v * 10 + (unsigned)(*p - '0');
    return v;
}

long long ParseI64(const char* p, const char* e) {
    bool neg = (p < e && *p == '-');
    if (neg) ++p;
    long long v = (long long)ParseU64(p, e);
    return neg ? -v : v;
}

void AppendPad(std::string& s, unsigned v, int width) {
    char b[12];
    for (int i = width - 1; i >= 0; --i) { b[i] = (char)('0' + v % 10); v /= 10; }
    s.append(b, (size_t)width);
}

/* ---------- Fechas ---------- */

const long long kEpochDiff = 11644473600LL;   // segundos entre 1601-01-01 y 1970-01-01

long long FtToUnix(const FILETIME& ft) {
    ULARGE_INTEGER u;
    u.LowPart = ft.dwLowDateTime;
    u.HighPart = ft.dwHighDateTime;
    return (long long)(u.QuadPart / 10000000ULL) - kEpochDiff;
}

bool UnixToFt(long long t, FILETIME& ft) {
    if (t < -kEpochDiff) return false;
    ULARGE_INTEGER u;
    u.QuadPart = (unsigned long long)(t + kEpochDiff) * 10000000ULL;
    ft.dwLowDateTime = u.LowPart;
    ft.dwHighDateTime = u.HighPart;
    return true;
}

/* TC espera hora local en formato DOS empaquetado: (fecha << 16) | hora.
   Fuera del rango 1980..2107 se usa 1980-01-01 */
int UnixToDos(long long t) {
    const int kMin = 0x00210000;
    FILETIME ft, lft;
    WORD d, tm;
    if (!UnixToFt(t, ft) || !FileTimeToLocalFileTime(&ft, &lft) ||
        !FileTimeToDosDateTime(&lft, &d, &tm))
        return kMin;
    return (int)(((DWORD)d << 16) | tm);
}

long long NowUnix() {
    FILETIME ft;
    GetSystemTimeAsFileTime(&ft);
    return FtToUnix(ft);
}

/* ---------- E/S de archivos ---------- */

bool WriteAll(HANDLE h, const void* p, size_t n) {
    const unsigned char* b = (const unsigned char*)p;
    while (n) {
        DWORD chunk = n > (1u << 26) ? (1u << 26) : (DWORD)n, w = 0;
        if (!WriteFile(h, b, chunk, &w, NULL) || !w) return false;
        b += w; n -= w;
    }
    return true;
}

bool ReadAll(HANDLE h, void* p, size_t n) {
    unsigned char* b = (unsigned char*)p;
    while (n) {
        DWORD chunk = n > (1u << 26) ? (1u << 26) : (DWORD)n, r = 0;
        if (!ReadFile(h, b, chunk, &r, NULL) || !r) return false;
        b += r; n -= r;
    }
    return true;
}

void Put32(unsigned char* b, unsigned long long v) { for (int i = 0; i < 4; ++i) b[i] = (unsigned char)(v >> (8 * i)); }
void Put64(unsigned char* b, unsigned long long v) { for (int i = 0; i < 8; ++i) b[i] = (unsigned char)(v >> (8 * i)); }
unsigned long long Get(const unsigned char* b, int n) {
    unsigned long long v = 0;
    for (int i = 0; i < n; ++i) v |= (unsigned long long)b[i] << (8 * i);
    return v;
}

/* ---------- Apertura / lectura del catálogo ---------- */

void ParseIndex(const char* p, const char* end, Archive* a) {
    auto tab = [](const char* s, const char* e) -> const char* {
        return s < e ? (const char*)memchr(s, '\t', (size_t)(e - s)) : NULL;
    };
    while (p < end) {
        const char* nl   = (const char*)memchr(p, '\n', (size_t)(end - p));
        const char* le   = nl ? nl : end;
        const char* next = nl ? nl + 1 : end;
        if (le > p && le[-1] == '\r') --le;

        const char* t1 = tab(p, le);
        const char* t2 = t1 ? tab(t1 + 1, le) : NULL;
        const char* t3 = t2 ? tab(t2 + 1, le) : NULL;
        if (t3 && t1 > p) {
            Item it;
            it.name        = FromUtf8(p, (size_t)(t1 - p));
            it.e.size      = ParseU64(t1 + 1, t2);
            it.e.unixTime  = ParseI64(t2 + 1, t3);
            it.e.attr      = (DWORD)ParseU64(t3 + 1, le);
            a->items.push_back(std::move(it));
        }
        p = next;
    }
}

int LoadArchive(const std::wstring& path, Archive*& out) {
    out = NULL;
    HANDLE h = CreateFileW(LongPath(path).c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE,
                           NULL, OPEN_EXISTING, FILE_FLAG_SEQUENTIAL_SCAN, NULL);
    if (h == INVALID_HANDLE_VALUE) return E_EOPEN;

    LARGE_INTEGER sz;
    unsigned char hdr[kHdrSize];
    if (!GetFileSizeEx(h, &sz) || sz.QuadPart < (LONGLONG)kHdrSize) { CloseHandle(h); return E_BAD_ARCHIVE; }
    if (!ReadAll(h, hdr, kHdrSize)) { CloseHandle(h); return E_EREAD; }
    if (memcmp(hdr, kMagic, 6) != 0) { CloseHandle(h); return E_BAD_ARCHIVE; }

    unsigned long long ulen = Get(hdr + 8, 8), clen = Get(hdr + 16, 8);
    unsigned long long crc  = Get(hdr + 24, 4);
    if (ulen > kMaxIndex || clen > kMaxIndex || clen != (unsigned long long)sz.QuadPart - kHdrSize) {
        CloseHandle(h);
        return E_BAD_ARCHIVE;
    }

    Archive* a = new Archive();
    if (ulen) {
        std::vector<unsigned char> comp((size_t)clen);
        if (!ReadAll(h, comp.data(), comp.size())) { CloseHandle(h); delete a; return E_EREAD; }

        std::vector<char> raw((size_t)ulen);
        mz_ulong dl = (mz_ulong)ulen;
        if (mz_uncompress((unsigned char*)raw.data(), &dl, comp.data(), (mz_ulong)clen) != MZ_OK ||
            dl != (mz_ulong)ulen ||
            (unsigned long long)(mz_crc32(MZ_CRC32_INIT, (const unsigned char*)raw.data(), raw.size()) & 0xFFFFFFFFu) != crc) {
            CloseHandle(h); delete a;
            return E_BAD_DATA;
        }
        comp.clear(); comp.shrink_to_fit();
        ParseIndex(raw.data(), raw.data() + raw.size(), a);
    }
    CloseHandle(h);
    out = a;
    return 0;
}

/* ---------- Entrega de cabeceras ---------- */

/* Campos numéricos comunes de THeaderDataEx / THeaderDataExW */
template <class H> void FillNum(H* h, const Item& it) {
    h->Flags        = 0;
    h->PackSize     = 0;
    h->PackSizeHigh = 0;
    h->UnpSize      = (unsigned int)(it.e.size & 0xFFFFFFFFULL);
    h->UnpSizeHigh  = (unsigned int)(it.e.size >> 32);
    h->HostOS       = 0;
    h->FileCRC      = 0;
    h->FileTime     = UnixToDos(it.e.unixTime);
    h->UnpVer       = 0;
    h->Method       = 0;
    h->FileAttr     = (int)it.e.attr;
    h->CmtBuf       = NULL;
    h->CmtBufSize = h->CmtSize = h->CmtState = 0;
}

void FillNum(THeaderData* h, const Item& it) {
    h->Flags    = 0;
    h->PackSize = 0;
    h->UnpSize  = it.e.size > 0x7FFFFFFFULL ? 0x7FFFFFFF : (int)it.e.size;
    h->HostOS   = 0;
    h->FileCRC  = 0;
    h->FileTime = UnixToDos(it.e.unixTime);
    h->UnpVer   = 0;
    h->Method   = 0;
    h->FileAttr = (int)it.e.attr;
    h->CmtBuf   = NULL;
    h->CmtBufSize = h->CmtSize = h->CmtState = 0;
}

/* Versiones ANSI: se saltan las entradas cuyo nombre no cabe/convierte en la página de códigos actual */
template <class H> int ReadAnsi(Archive* a, H* d, int cap) {
    while (a->pos < a->items.size()) {
        const Item& it = a->items[a->pos];
        if (ToAnsi(it.name, d->FileName, cap)) {
            FillNum(d, it);
            return 0;
        }
        ++a->pos;
    }
    return E_END_ARCHIVE;
}

/* ---------- Extracción (stub) ---------- */

std::string BuildStub(const Item& it) {
    std::string s("\xEF\xBB\xBF");   // BOM UTF-8
    s += "LSTZ catalog entry (sin contenido real)\r\nPath: ";
    s += ToUtf8(it.name);
    s += "\r\nSize: ";
    AppendU64(s, it.e.size);
    s += " bytes\r\nModified (UTC): ";
    FILETIME ft; SYSTEMTIME st;
    if (UnixToFt(it.e.unixTime, ft) && FileTimeToSystemTime(&ft, &st)) {
        AppendPad(s, st.wYear, 4);   s += '-';
        AppendPad(s, st.wMonth, 2);  s += '-';
        AppendPad(s, st.wDay, 2);    s += ' ';
        AppendPad(s, st.wHour, 2);   s += ':';
        AppendPad(s, st.wMinute, 2); s += ':';
        AppendPad(s, st.wSecond, 2);
    } else s += "?";
    s += "\r\n";
    return s;
}

int Process(HANDLE h, int op, const std::wstring& destPath, bool hasPath, const std::wstring& destName) {
    Archive* a = (Archive*)h;
    if (!a) return E_BAD_DATA;
    if (a->pos >= a->items.size()) return E_END_ARCHIVE;
    const Item& it = a->items[a->pos++];
    if (op != PK_EXTRACT) return 0;     // PK_SKIP y PK_TEST: OK sin hacer nada

    std::wstring full = destName;
    if (hasPath) {
        full = destPath;
        if (!full.empty() && full.back() != L'\\') full += L'\\';
        full += destName;
    }
    if (it.e.attr & FILE_ATTRIBUTE_DIRECTORY) {
        CreateDirectoryW(LongPath(full).c_str(), NULL);
        return 0;
    }
    HANDLE f = CreateFileW(LongPath(full).c_str(), GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) return E_ECREATE;
    std::string stub = BuildStub(it);
    bool ok = WriteAll(f, stub.data(), stub.size());
    CloseHandle(f);
    return ok ? 0 : E_EWRITE;
}

/* ---------- Creación del catálogo ---------- */

bool Progress(const std::wstring& name) {
    if (g_procW) return g_procW((WCHAR*)name.c_str(), 0) != 0;
    if (g_procA) {
        char buf[1024];
        if (!ToAnsi(name, buf, sizeof(buf))) buf[0] = 0;
        return g_procA(buf, 0) != 0;
    }
    return true;
}

/* Consulta al callback cada 256 entradas; false = el usuario canceló */
bool Tick(const std::wstring& name) {
    return ((++g_tick) & 0xFF) != 1 || Progress(name);
}

bool StatPath(const std::wstring& full, Entry& e) {
    WIN32_FILE_ATTRIBUTE_DATA d;
    if (!GetFileAttributesExW(LongPath(full).c_str(), GetFileExInfoStandard, &d)) return false;
    e.attr     = d.dwFileAttributes;
    e.size     = (e.attr & FILE_ATTRIBUTE_DIRECTORY) ? 0 : (((unsigned long long)d.nFileSizeHigh << 32) | d.nFileSizeLow);
    e.unixTime = FtToUnix(d.ftLastWriteTime);
    return true;
}

bool Scan(EntryMap& m, const std::wstring& rel, const std::wstring& full) {
    WIN32_FIND_DATAW fd;
    HANDLE h = FindFirstFileW(LongPath(full + L"\\*").c_str(), &fd);
    if (h == INVALID_HANDLE_VALUE) return true;
    bool ok = true;
    do {
        if (fd.cFileName[0] == L'.' && (!fd.cFileName[1] || (fd.cFileName[1] == L'.' && !fd.cFileName[2]))) continue;
        std::wstring r = rel + L"\\" + fd.cFileName;
        Entry e;
        e.attr     = fd.dwFileAttributes;
        e.size     = (e.attr & FILE_ATTRIBUTE_DIRECTORY) ? 0 : (((unsigned long long)fd.nFileSizeHigh << 32) | fd.nFileSizeLow);
        e.unixTime = FtToUnix(fd.ftLastWriteTime);
        m[r] = e;
        if (!Tick(r)) { ok = false; break; }
        // No se sigue junctions/symlinks de directorio para evitar ciclos
        if ((e.attr & FILE_ATTRIBUTE_DIRECTORY) && !(e.attr & FILE_ATTRIBUTE_REPARSE_POINT))
            if (!Scan(m, r, full + L"\\" + fd.cFileName)) { ok = false; break; }
    } while (FindNextFileW(h, &fd));
    FindClose(h);
    return ok;
}

void AddAncestors(EntryMap& m, const std::wstring& base) {
    std::vector<std::wstring> keys;
    keys.reserve(m.size());
    for (EntryMap::const_iterator i = m.begin(); i != m.end(); ++i) keys.push_back(i->first);
    for (size_t k = 0; k < keys.size(); ++k) {
        size_t p = 0;
        while ((p = keys[k].find(L'\\', p)) != std::wstring::npos) {
            std::wstring anc = keys[k].substr(0, p);
            if (!m.count(anc)) {
                Entry e;
                if (!StatPath(base + anc, e)) { e.attr = FILE_ATTRIBUTE_DIRECTORY; e.unixTime = NowUnix(); }
                m[anc] = e;
            }
            ++p;
        }
    }
}

void AppendLine(std::string& idx, const std::wstring& path, const Entry& e) {
    idx += ToUtf8(path);
    idx += '\t'; AppendU64(idx, e.size);
    idx += '\t'; AppendI64(idx, e.unixTime);
    idx += '\t'; AppendU64(idx, e.attr);
    idx += '\n';
}

int PackImpl(const std::wstring& packed, std::wstring sub, const std::wstring& src,
             const std::vector<std::wstring>& list, int flags) {
    // Un catálogo es solo un índice: mover (borrar origen) está prohibido
    if (flags & PK_PACK_MOVE_FILES) return E_NOT_SUPPORTED;

    g_tick = 0;
    std::wstring base = src;
    if (!base.empty() && base.back() != L'\\') base += L'\\';

    EntryMap m;
    for (size_t i = 0; i < list.size(); ++i) {
        std::wstring rel = list[i];
        while (!rel.empty() && rel.back() == L'\\') rel.pop_back();
        if (rel.empty()) continue;

        Entry e;
        if (!StatPath(base + rel, e)) continue;
        m[rel] = e;
        if (!Tick(rel)) return E_EABORTED;

        if ((e.attr & FILE_ATTRIBUTE_DIRECTORY) && !(e.attr & FILE_ATTRIBUTE_REPARSE_POINT)) {
            // TC normalmente ya expande los directorios: si el siguiente elemento
            // de la lista cuelga de este, no se vuelve a recorrer en disco.
            bool expanded = i + 1 < list.size() && list[i + 1].size() > rel.size() &&
                            _wcsnicmp(list[i + 1].c_str(), rel.c_str(), rel.size()) == 0 &&
                            list[i + 1][rel.size()] == L'\\';
            if (!expanded && !Scan(m, rel, base + rel)) return E_EABORTED;
        }
    }
    if (m.empty()) return E_NO_FILES;
    AddAncestors(m, base);

    while (!sub.empty() && (sub[0] == L'\\' || sub[0] == L'/')) sub.erase(0, 1);
    while (!sub.empty() && (sub.back() == L'\\' || sub.back() == L'/')) sub.pop_back();

    std::string idx;
    idx.reserve(m.size() * 96);
    if (!sub.empty()) {
        Entry d;
        d.attr = FILE_ATTRIBUTE_DIRECTORY;
        d.unixTime = NowUnix();
        size_t p = 0;
        while (true) {
            p = sub.find(L'\\', p);
            AppendLine(idx, sub.substr(0, p), d);
            if (p == std::wstring::npos) break;
            ++p;
        }
        sub += L'\\';
    }
    for (EntryMap::const_iterator i = m.begin(); i != m.end(); ++i) AppendLine(idx, sub + i->first, i->second);

    if (idx.size() > kMaxIndex) return E_NO_MEMORY;

    mz_ulong cl = mz_compressBound((mz_ulong)idx.size());
    std::vector<unsigned char> comp(cl);
    if (mz_compress2(comp.data(), &cl, (const unsigned char*)idx.data(), (mz_ulong)idx.size(), 9) != MZ_OK)
        return E_BAD_DATA;

    unsigned char hdr[kHdrSize];
    memset(hdr, 0, sizeof(hdr));
    memcpy(hdr, kMagic, 6);
    Put64(hdr + 8, idx.size());
    Put64(hdr + 16, cl);
    Put32(hdr + 24, mz_crc32(MZ_CRC32_INIT, (const unsigned char*)idx.data(), idx.size()) & 0xFFFFFFFFu);

    // Se escribe en un temporal y se reemplaza al final: un fallo no destruye un catálogo previo
    std::wstring tmp = packed + L".tmp";
    HANDLE f = CreateFileW(LongPath(tmp).c_str(), GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) return E_ECREATE;
    bool ok = WriteAll(f, hdr, kHdrSize) && WriteAll(f, comp.data(), cl);
    ok = (CloseHandle(f) != 0) && ok;
    if (!ok) { DeleteFileW(LongPath(tmp).c_str()); return E_EWRITE; }
    if (!MoveFileExW(LongPath(tmp).c_str(), LongPath(packed).c_str(), MOVEFILE_REPLACE_EXISTING)) {
        DeleteFileW(LongPath(tmp).c_str());
        return E_EWRITE;
    }
    return 0;
}

} // namespace

/* ======================= Exportaciones WCX ======================= */

WCX_API(HANDLE) OpenArchiveW(tOpenArchiveDataW* d) {
    try {
        Archive* a = NULL;
        int r = LoadArchive(d->ArcName ? d->ArcName : L"", a);
        d->OpenResult = r;
        d->CmtSize = d->CmtState = 0;
        return r == 0 ? (HANDLE)a : NULL;
    } catch (...) {
        d->OpenResult = E_NO_MEMORY;
        return NULL;
    }
}

WCX_API(HANDLE) OpenArchive(tOpenArchiveData* d) {
    try {
        Archive* a = NULL;
        int r = LoadArchive(FromAnsi(d->ArcName), a);
        d->OpenResult = r;
        d->CmtSize = d->CmtState = 0;
        return r == 0 ? (HANDLE)a : NULL;
    } catch (...) {
        d->OpenResult = E_NO_MEMORY;
        return NULL;
    }
}

WCX_API(int) ReadHeaderExW(HANDLE h, THeaderDataExW* d) {
    Archive* a = (Archive*)h;
    if (!a) return E_BAD_DATA;
    // Nombres de 1024+ caracteres no caben en la estructura: se omiten
    while (a->pos < a->items.size() && a->items[a->pos].name.size() >= 1024) ++a->pos;
    if (a->pos >= a->items.size()) return E_END_ARCHIVE;
    const Item& it = a->items[a->pos];
    memset(d, 0, sizeof(*d));
    lstrcpynW(d->FileName, it.name.c_str(), 1024);
    FillNum(d, it);
    return 0;
}

WCX_API(int) ReadHeaderEx(HANDLE h, THeaderDataEx* d) {
    Archive* a = (Archive*)h;
    if (!a) return E_BAD_DATA;
    memset(d, 0, sizeof(*d));
    return ReadAnsi(a, d, 1024);
}

WCX_API(int) ReadHeader(HANDLE h, THeaderData* d) {
    Archive* a = (Archive*)h;
    if (!a) return E_BAD_DATA;
    memset(d, 0, sizeof(*d));
    return ReadAnsi(a, d, 260);
}

WCX_API(int) ProcessFileW(HANDLE h, int op, WCHAR* destPath, WCHAR* destName) {
    try {
        return Process(h, op, destPath ? destPath : L"", destPath != NULL, destName ? destName : L"");
    } catch (...) { return E_NO_MEMORY; }
}

WCX_API(int) ProcessFile(HANDLE h, int op, char* destPath, char* destName) {
    try {
        return Process(h, op, FromAnsi(destPath), destPath != NULL, FromAnsi(destName));
    } catch (...) { return E_NO_MEMORY; }
}

WCX_API(int) CloseArchive(HANDLE h) {
    delete (Archive*)h;
    return 0;
}

WCX_API(int) PackFilesW(WCHAR* packed, WCHAR* sub, WCHAR* src, WCHAR* addList, int flags) {
    try {
        std::vector<std::wstring> list;
        for (WCHAR* p = addList; p && *p; p += lstrlenW(p) + 1) list.push_back(p);
        return PackImpl(packed ? packed : L"", sub ? sub : L"", src ? src : L"", list, flags);
    } catch (...) { return E_NO_MEMORY; }
}

WCX_API(int) PackFiles(char* packed, char* sub, char* src, char* addList, int flags) {
    try {
        std::vector<std::wstring> list;
        for (char* p = addList; p && *p; p += strlen(p) + 1) list.push_back(FromAnsi(p));
        return PackImpl(FromAnsi(packed), FromAnsi(sub), FromAnsi(src), list, flags);
    } catch (...) { return E_NO_MEMORY; }
}

WCX_API(int) GetPackerCaps(void) {
    return PK_CAPS_NEW | PK_CAPS_MULTIPLE | PK_CAPS_SEARCHTEXT;
}

WCX_API(void) SetChangeVolProc(HANDLE, tChangeVolProc) {}
WCX_API(void) SetChangeVolProcW(HANDLE, tChangeVolProcW) {}
WCX_API(void) SetProcessDataProc(HANDLE, tProcessDataProc p)   { g_procA = p; }
WCX_API(void) SetProcessDataProcW(HANDLE, tProcessDataProcW p) { g_procW = p; }
