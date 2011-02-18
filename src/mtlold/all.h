namespace Minisat{
template<class V, class T>
static inline void remove(V& ts, const T& t);

template<class V, class T>
static inline bool find(V& ts, const T& t);

template<class Comp>
class BasicHeap {
  public:
    BasicHeap(const C& c);

    int  size      ()                     const;
    bool empty     ()                     const;
    int  operator[](int index)            const;
    void clear     (bool dealloc = false)      ;
    void insert    (int n)                     ;
    int  removeMin ()                          ;
};

template<class T>
class bvec {
   public:
    void     clear  (bool dealloc = false);

    // Constructors:
    altvec(void);
    altvec(int size);
    altvec(int size, const T& pad);
   ~altvec(void);

    // Ownership of underlying array:
    operator T*       (void);           // (unsafe but convenient)
    operator const T* (void) const;

    // Size operations:
    int      size   (void) const;

    void     pop    (void);
    void     push   (const T& elem);
    void     push   ();

    void     shrink (int nelems);
    void     shrink_(int nelems);
    void     growTo (int size);
    void     growTo (int size, const T& pad);
    void     capacity (int size);

    const T& last  (void) const;
    T&       last  (void);

    // Vector interface:
    const T& operator [] (int index) const;
    T&       operator [] (int index);

    void copyTo(altvec<T>& copy) const;
    void moveTo(altvec<T>& dest);
};

template<class Comp>
class Heap {
  public:
    Heap(const Comp& c);

    int  size      ()          const;
    bool empty     ()          const;
    bool inHeap    (int n)     const;
    int  operator[](int index) const;

    void decrease  (int n);
    // RENAME WHEN THE DEPRECATED INCREASE IS REMOVED.
    void increase_ (int n);
    void insert(int n);
    int  removeMin();
    void clear(bool dealloc = false);
    // Fool proof variant of insert/decrease/increase
    void update (int n);
    // Delete elements from the heap using a given filter function (-object).
    // *** this could probaly be replaced with a more general "buildHeap(vec<int>&)" method ***
    template <class F>
    void filter(const F& filt);
};

template<class K, class D, class H = Hash<K>, class E = Equal<K> >
class Map {
    public:

     Map ();
     Map (const H& h, const E& e);
    ~Map ();

    void insert (const K& k, const D& d);
    bool peek   (const K& k, D& d);
    void remove (const K& k);
    void clear  ();
};

template <class T>
class Queue {
public:
    Queue(void);

    void insert(T x);
    T    peek  () const;
    void pop   ();

    void clear(bool dealloc = false);
    int  size(void);
    const T& operator [] (int index) const;
};

template<class T>
class vec {
   public:
    // Types:
    typedef int Key;
    typedef T   Datum;

    // Constructors:
    vec(void);
    vec(int size);
    vec(int size, const T& pad);
    vec(T* array, int size);       // (takes ownership of array -- will be deallocated with 'free()')
   ~vec(void);

    // Ownership of underlying array:
    T*       release  (void);
    operator T*       (void);               // (unsafe but convenient)
    operator const T* (void) const;

    // Size operations:
    int      size   (void) const;
    void     shrink (int nelems);
    void     shrink_(int nelems);
    void     pop    (void);
    void     growTo (int size);
    void     growTo (int size, const T& pad);
    void     clear  (bool dealloc = false);
    void     capacity (int size);

    // Stack interface:
    void     push  (void);
    void     push  (const T& elem);
    void     push_ (const T& elem);

    const T& last  (void) const;
    T&       last  (void);

    // Vector interface:
    const T& operator [] (int index) const;
    T&       operator [] (int index);

    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const;
    void moveTo(vec<T>& dest);
};


}
