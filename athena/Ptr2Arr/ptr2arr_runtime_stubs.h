/* Ptr2Arr runtime stubs */
static inline char *intr_strncpy(char *dest, const char *src, size_t n) {
    size_t i = 0;
    while (i < n && src[i] != '\0') {
        dest[i] = src[i];
        ++i;
    }
    for (; i < n; ++i) {
        dest[i] = '\0';
    }
    return dest;
}

static inline char *r_strncpy(char *dest, const char *src, size_t n) {
    return intr_strncpy(dest, src, n);
}

static inline char *r_strcpy(char *dest, const char *src) {
    size_t i = 0;
    while (src[i] != '\0') {
        dest[i] = src[i];
        ++i;
    }
    dest[i] = '\0';
    return dest;
}

static inline char *r_strcat(char *dest, const char *src) {
    size_t i = 0;
    while (dest[i] != '\0') {
        ++i;
    }
    size_t j = 0;
    while (src[j] != '\0') {
        dest[i++] = src[j++];
    }
    dest[i] = '\0';
    return dest;
}

static inline char *r_strncat(char *dest, const char *src, size_t n) {
    size_t i = 0;
    while (dest[i] != '\0') {
        ++i;
    }
    size_t j = 0;
    while (j < n && src[j] != '\0') {
        dest[i++] = src[j++];
    }
    dest[i] = '\0';
    return dest;
}

static inline void *r_memcpy(void *dest, const void *src, size_t n) {
    char *d = (char *)dest;
    const char *s = (const char *)src;
    for (size_t i = 0; i < n; ++i) {
        d[i] = s[i];
    }
    return dest;
}
