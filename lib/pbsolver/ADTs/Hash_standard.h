#ifndef Hash_standard_h
#define Hash_standard_h


namespace MiniSatPP {
//=================================================================================================
// Some Primes...


static int prime_twins[25] = { 31, 73, 151, 313, 643, 1291, 2593, 5233, 10501, 21013, 42073, 84181, 168451, 337219, 674701, 1349473, 2699299, 5398891, 10798093, 21596719, 43193641, 86387383, 172775299, 345550609, 691101253 };


//=================================================================================================
// Standard hash parameters:


template <class K> struct Hash  { unsigned int operator () (const K& key)                 const { return key.hash(); } };
template <class K> struct Equal { bool operator () (const K& key1, const K& key2) const { return key1 == key2; } };

template <class K> struct Hash_params {
    static unsigned int hash (K key)          { return Hash <K>()(key);        }
    static bool equal(K key1, K key2) { return Equal<K>()(key1, key2); }
};


//=================================================================================================


// DEFINE PATTERN MACRO:
//
// 'code' should use 'key' (hash) or 'key1'/'key2' (equal) to access the elements. The last statement should be a return.
//
#define DefineHash( type, code) template <> struct Hash<type>  { unsigned int operator () (type key) const { code } };
#define DefineEqual(type, code) template <> struct Equal<type> { bool operator () (type key1, type key2) const { code } };


// PAIRS:

template <class S, class T> struct Hash <Pair<S,T> > { unsigned int operator () (const Pair<S,T>& key)                         const { return Hash<S>()(key.fst) ^ Hash<T>()(key.snd); } };
template <class S, class T> struct Equal<Pair<S,T> > { bool operator () (const Pair<S,T>& key1, const Pair<S,T>& key2) const { return Equal<S>()(key1.fst, key2.fst) && Equal<T>()(key1.snd, key2.snd); } };


// POINTERS:

#ifdef LP64
template <class K> struct Hash<const K*> { unsigned int operator () (const K* key) const { unsigned int tmp = reinterpret_cast<unsigned int>(key); return (unsigned)((tmp >> 32) ^ tmp); } };
template <class K> struct Hash<K*>       { unsigned int operator () (K* key)       const { unsigned int tmp = reinterpret_cast<unsigned int>(key); return (unsigned)((tmp >> 32) ^ tmp); } };
#else
template <class K> struct Hash<const K*> { unsigned int operator () (const K* key) const { return reinterpret_cast<unsigned int>(key); } };
template <class K> struct Hash<K*>       { unsigned int operator () (K* key)       const { return reinterpret_cast<unsigned int>(key); } };
#endif

// C-STRINGS:

DefineHash (const char*, unsigned int v = 0; for (int i = 0; key[i] != '\0'; i++) v = (v << 3) + key[i]; return v;)
DefineEqual(const char*, if (key1 == key2) return true; else return strcmp(key1, key2) == 0;)
DefineHash (char*, unsigned int v = 0; for (int i = 0; key[i] != '\0'; i++) v = (v << 3) + key[i]; return v;)
DefineEqual(char*, if (key1 == key2) return true; else return strcmp(key1, key2) == 0;)


// INTEGER TYPES:

DefineHash(char  , return (unsigned int)key;)
DefineHash(signed char , return (unsigned int)key;)
DefineHash(unsigned char , return (unsigned int)key;)
DefineHash(short , return (unsigned int)key;)
DefineHash(unsigned short, return (unsigned int)key;)
DefineHash(int   , return (unsigned int)key;)
DefineHash(unsigned int  , return (unsigned int)key;)
#ifdef LP64
DefineHash(long  , return (unsigned int)(((unsigned long)key >> 32) ^ key);)
DefineHash(unsigned long , return (unsigned int)(((unsigned long)key >> 32) ^ key);)
#else
DefineHash(long  , return (unsigned int)key;)
DefineHash(unsigned long , return (unsigned int)key;)
#endif
DefineHash(int64 , return (unsigned int)(((uint64)key >> 32) ^ key);)
DefineHash(uint64, return (unsigned int)(((uint64)key >> 32) ^ key);)


//=================================================================================================
}
#endif
