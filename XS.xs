#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

#define MAGIC	1

enum order {
    LESS = 1,
    MORE,
    LT,
    GT,
    CODE_ORDER,
    MAX_ORDER
};

enum elements {
    SCALAR = 1,
    ARRAY,
    HASH,
    METHOD,
    OBJECT,
    FUNCTION,
    ANY_ELEM,
    MAX_ELEMENTS
};

typedef struct heap {
    SV **values;	/* The values the user stored in the heap */
    SV **keys;		/* The corresponding keys, but only if wrapped == 1 */
    SV *hkey;		/* An SV used in finding a key for a value.
                           E.g. the hash key for element type Hash */
    SV *order_sv;	/* Code reference to compare keys for the CODE order */
    SV *infinity;	/* The infinity for the given order, can be NULL */
    SV *user_data;	/* Associated data, only for the user */
    UV used;		/* How many values/keys are used+1 (index 0 unused) */
    UV allocated;	/* How many values/keys are allocated */
    UV max_count;	/* Maximum heap size, 0 means unlimited */
    I32 aindex;		/* A value used for indexing the key for a value */
    int wrapped;	/* True if keys are stored seperate from values */
    int fast;		/* True means that keys are scalars, not SV's */
    int has_values;	/* SV values in the SV array. False for fast scalars */
    int dirty;		/* "dirty" option was given and true */
    int can_die;	/* Just remembers if the option was given,
			   This implementation is supposed to always be safe */
    int key_ops;        /* key_insert, _key_insert and key_absorb will work */
    int locked;
    enum order order;	/* Which order is used */
    enum elements elements; /* Element type */
} *heap;

/*
    O: not filed in
    X: Filled in, but not an SV (only happens for keys, if and only if fast)
    *: Filled in with an SV     (if and only if has_values)

    Possible flag combinations:
    wrapped fast has_values KV
      0       0      0	          Impossible
      1       0      0		  Impossible
      0       1      0      XO    scalar dirty order
      1       1      0		  Impossible
      0       0      1      O*    Normal heap
      1       0      1      **    Object/Any heap
     (0       1      1      X*    normal heap with dirty order) # dropped
      1       1      1      X*    Object/Any heap with dirty order


      looks "wrapped" to the outside world for the last 3 cases
 */

static void extend(heap h) {
    h->allocated = 2*(h->used+4);
    if (h->fast) {
        NV *tmp;
        tmp = (NV *) h->keys;
        Renew(tmp, h->allocated, NV);
        h->keys = (SV **) tmp;
        if (h->has_values) Renew(h->values, h->allocated, SV *);
    } else {
        if (h->wrapped) Renew(h->keys, h->allocated, SV *);
        Renew(h->values, h->allocated, SV *);
    }
}

/* target is lowercase, ends in 0, and lengths are already equal */
static int low_eq(const char *name, const char *target) {
    while (*target) {
        if (toLOWER(*name) != *target++) return 0;
        name++;
    }
    return 1;
}

static const char *elements_name(heap h) {
    switch(h->elements) {
      case SCALAR:   return "Scalar";
      case ARRAY:    return "Array";
      case HASH:     return "Hash";
      case METHOD:   return "Method";
      case OBJECT:   return "Object";
      case FUNCTION: return "Function";
      case ANY_ELEM: return "Any";
      case 0: croak("Element type is unspecified");
    }
    croak("Assertion: Impossible element type %d", h->elements);
}

static const char *order_name(heap h) {
    switch(h->order) {
      case LESS: return "<";
      case MORE: return ">";
      case LT:   return "lt";
      case GT:   return "gt";
      case CODE_ORDER: return "CODE";
      case 0: croak("Order type is unspecified");
    }
    croak("Assertion: Impossible order type %d", h->elements);
}

/*  KEY only gets called if h->fast == 0 */
#define KEY(h, i) ((h)->wrapped ? (h)->keys[i] : fetch_key((h),(h)->values[i]))
/* FKEY only gets called if h->fast == 1 */
#define FKEY(type, h, i)	(((type *)(h)->keys)[i])
/* key is returned with the refcount unincremented,
   key will not have get magic applied */
static SV *fetch_key(heap h, SV *value) {
    switch(h->elements) {
        AV *av;
        HV *hv;
        HE *he;
        SV **fetched, *key;
        I32 start, count;
      case SCALAR:
        return value;
      case ARRAY:
        /* mm, can a tied access change the stack base ? */
        if (!SvROK(value)) croak("Not a reference");
        av = (AV*) SvRV(value);
        if (SvTYPE(av) != SVt_PVAV) croak("Not an ARRAY reference");
        fetched = av_fetch(av, h->aindex, 0);
        return fetched ? *fetched : &PL_sv_undef;
      case HASH:
        if (!SvROK(value)) croak("Not a reference");
        hv = (HV*) SvRV(value);
        if (SvTYPE(hv) != SVt_PVHV) croak("Not a HASH reference");
        he = hv_fetch_ent(hv, h->hkey, 0, h->aindex);
        if (he) {
            /* HASH value for magical hashes seem to jump around */
            if (!h->aindex && !(MAGIC && SvMAGICAL(hv))) 
                h->aindex = HeHASH(he);
            return HeVAL(he);
        } else {
            return &PL_sv_undef;
        }
      case OBJECT:
        if (!h->hkey) croak("Element type 'Object' without key method");
        /* FALLTHROUGH */
      case METHOD:
          {
              dSP;
              const char *name;

              start = (SP) - PL_stack_base;
              name = SvPV_nolen(h->hkey);
              PUSHMARK(SP);
              XPUSHs(value);
              PUTBACK;
              count = call_method(name, G_SCALAR);
              if (count != 1) croak("Forced scalar context call succeeded in returning %d values. This is impossible", (int) count);

              SPAGAIN;
              key = POPs;
              if (start != (SP) - PL_stack_base) croak("Stack base changed");
              PUTBACK;
              /* Stack is back, but can have been reallocated ! */
              return key;
          }
      case ANY_ELEM:
        if (!h->hkey) croak("Element type 'Any' without key code");
        /* FALLTHROUGH */
      case FUNCTION:
          {
              dSP;

              start = (SP) - PL_stack_base;
              PUSHMARK(SP);
              XPUSHs(value);
              PUTBACK;
              count = call_sv(h->hkey, G_SCALAR);
              if (count != 1) croak("Forced scalar context call succeeded in returning %d values. This is impossible", (int) count);

              SPAGAIN;
              key = POPs;
              if (start != (SP) - PL_stack_base) croak("Stack base changed");
              PUTBACK;
              /* Stack is back, but can have been reallocated ! */
              return key;
          }
      default:
        croak("fetch_key not implemented for element type '%s'",
              elements_name(h));
    }
    croak("fetch_key does not return for element type '%s'",
          elements_name(h));
}

/* should be able to handle get magic if needed, 
   but will normally be called without */
static int less(pTHX_ heap h, SV *l, SV *r) {
    SV *result;
    I32 start, count;
    dSP;

    start = (SP) - PL_stack_base;
    if (h->order == CODE_ORDER) { PUSHMARK(SP); }
    XPUSHs(l);
    XPUSHs(r);
    PUTBACK;
    switch(h->order) {
      case LESS:
        pp_lt();
        break;
      case MORE:
        pp_gt();
        break;
      case LT:
        pp_slt();
        break;
      case GT:
        pp_sgt();
        break;
      case CODE_ORDER:
        count = call_sv(h->order_sv, G_SCALAR);
        if (count != 1) croak("Forced scalar context call succeeded in returning %d values. This is impossible", (int) count);
        break;
      default:
        croak("less not implemented for order type '%s'", order_name(h));
    }
    SPAGAIN;
    result = POPs;
    if (start != (SP) - PL_stack_base) croak("Stack base changed");
    PUTBACK;
    /* warn("comparing %"NVff" to %"NVff" -> %d", SvNV(l), SvNV(r), SvTRUE(result) ? 1 : 0); */
    if      (result == &PL_sv_yes) return 1;
    else if (result == &PL_sv_no)  return 0;
    /* This can also happen for pp_lt and co in case the value is overloaded */
    /* SvTRUE does mg_get (through sv_2bool) */
    else return SvTRUE(result) ? 1 : 0;
}

/* key and value have refcount not increaded at call */
static void key_insert(pTHX_ heap h, SV *key, SV *value) {
    UV p, pos, l, n;
    SV *new, *t1, *t2;
    int val_copied, key_copied;

    val_copied = 0;
    if (h->fast) {
        NV k;

        if (!key) {
            if (MAGIC && SvGMAGICAL(value)) {
                value = sv_mortalcopy(value);
                val_copied = 1;
            }
            key = fetch_key(h, value);
        }
        /* SvNV will handle get magic (though sv_2nv) */
        if      (h->order == LESS) k =  SvNV(key);
        else if (h->order == MORE) k = -SvNV(key);
        else croak("No fast %s order", order_name(h));

        if (h->used > h->max_count) {
            if (h->used < 2 || k <= FKEY(NV, h, 1)) return;
            /* Drop the old top and percolate the new value down */
            /* This is almost completely identical to extract_top, but
               I don't see a clean way to factor it out that preserves
               resistance agains crashes of less/fetch_key */
            NV key1, key2;
            n = h->used-1;
            l = 2;
            
            if (h->has_values) {
                new = val_copied ? SvREFCNT_inc(value) : newSVsv(value);
                t1 = h->values[1];
            }
            
            while (l < n) {
                key1 = FKEY(NV, h, l);
                key2 = FKEY(NV, h, l+1);
                if (key1 < k) {
                    if (key2 < key1) {
                        FKEY(NV, h, l/2) = key2;
                        l++;
                    } else {
                        FKEY(NV, h, l/2) = key1;
                    }
                } else if (key2 < k) {
                    FKEY(NV, h, l/2) = key2;
                    l++;
                } else break;
                if (h->has_values) h->values[l/2] = h->values[l];
                l *= 2;
            }
            if (l == n) {
                key1 = FKEY(NV, h, l);
                if (key1 < k) {
                    FKEY(NV, h, l/2) = key1;
                    if (h->has_values) h->values[l/2] = h->values[l];
                    l*= 2;
                }
            }
            l /= 2;
            FKEY(NV, h, l) = k;
            if (h->has_values) {
                h->values[l] = new;
                SvREFCNT_dec(t1);
            }
            return;
        }

        pos = h->used;
        if (h->used >= h->allocated) extend(h);
        if (h->has_values) {
            new = val_copied ? SvREFCNT_inc(value) : newSVsv(value);
            while (pos > 1 && 
                   k < (FKEY(NV, h, pos) = FKEY(NV, h, pos/2))) {
                h->values[pos] = h->values[pos/2];
                pos /= 2;
            }
            h->values[pos] = new;
        } else {
            while (pos > 1 && k < (FKEY(NV, h, pos) = FKEY(NV, h, pos/2)))
                pos /= 2;
        }
        FKEY(NV, h, pos) = k;
        h->used++;
        return;
    }

    /* h->fast == 0 */
    if (h->used < 2) {
        /* Handled seperately in order to avoid an unneeded key fetch */
        if (h->used != 1) croak("Assertion: negative sized heap");
        if (h->max_count < 1) return;
        if (h->allocated <= 1) extend(h);
        if (h->wrapped) {
            if (!key) {
                if (MAGIC && SvGMAGICAL(value)) {
                    value = sv_mortalcopy(value);
                    val_copied = 1;
                }
                key = fetch_key(h, value);
            }
            /* newSVsv does get magic */
            h->keys[1] = newSVsv(key);
        }
        h->values[1] = val_copied ? SvREFCNT_inc(value) : newSVsv(value);
        h->used = 2;
        return;
    }

    /* We are certain we will need the key now. Fetch it. */
    if (!key) {
        if (MAGIC && SvGMAGICAL(value)) {
            value = sv_mortalcopy(value);
            val_copied = 1;
        }
        key = fetch_key(h, value);
    }
    if (MAGIC && SvGMAGICAL(key)) {
        key = sv_mortalcopy(key);
        key_copied = 1;
    } else key_copied = 0;

    if (h->used > h->max_count) {
        if (!less(aTHX_ h, KEY(h, 1), key)) return;
        /* Drop the old top and percolate the new value down */
        /* This is almost completely identical to extract_top, but
           I don't see a clean way to factor it out that preserves
           resistance agains exceptions in less/fetch_key */
        SV *key1, *key2;

        n = h->used-1;
        l = 2;

        while (l < n) {
            key1 = KEY(h, l);
            if (MAGIC && SvGMAGICAL(key1)) key1 = sv_mortalcopy(key1);
            key2 = KEY(h, l+1);
            if (less(aTHX_ h, key1, key)) {
                if (less(aTHX_  h, key2, key1)) l++;
            } else if (less(aTHX_ h, key2, key)) l++;
            else break;
            l *= 2;
        }
        if (l == n) {
            key1 = KEY(h, l);
            if (less(aTHX_ h, key1, key)) l*= 2;
        }
        l /= 2;

        t1 = val_copied ? SvREFCNT_inc(value) : newSVsv(value);
        if (h->wrapped) {
            /* Assume newSVsv can't die since key will already have been
               (mortal)copied in case it's magic */
            key1 = key_copied ? SvREFCNT_inc(key) : newSVsv(key);
            while (l >= 1) {
                key2 = h->keys[l];
                t2   = h->values[l];
                h->keys[l] = key1;
                h->values[l] = t1;
                key1 = key2;
                t1 = t2;
                l /= 2;
            }
            SvREFCNT_dec(key1);
        } else {
            while (l >= 1) {
                t2 = h->values[l];
                h->values[l] = t1;
                t1 = t2;
                l /= 2;
            }
        }
        SvREFCNT_dec(t1);
        return;
    }
    pos = h->used;

    while (pos > 1 && less(aTHX_ h, key, KEY(h, pos/2))) pos /= 2;
    if (h->used >= h->allocated) extend(h);
    new = val_copied ? SvREFCNT_inc(value) : newSVsv(value);
    if (h->wrapped) {
        /* Assume newSVsv can't die since key will already have been
           (mortal)copied in case it's magic */
        key = key_copied ? SvREFCNT_inc(key) : newSVsv(key);
        for (p=h->used; p != pos; p/=2) {
            h->keys[p]   = h->keys[p/2];
            h->values[p] = h->values[p/2];
        }
        h->keys[pos] = key;
    } else {
        for (p=h->used; p != pos; p/=2) h->values[p] = h->values[p/2];
    }
    h->values[pos] = new;
    h->used++;
}

/* Returns the top value with the refcount still increased 
   Only to be called if there is at least element, so with h->used >= 2 */
static SV *extract_top(pTHX_ heap h) {
    SV *t1, *t2;
    UV l, n;

    n = h->used-2;
    l = 2;

    if (h->fast) {
        NV key, key1, key2;

        key = FKEY(NV, h, --h->used);
        if (h->has_values) t1 = h->values[1];
        else if (h->order == LESS) t1 = newSVnv( FKEY(NV, h, 1));
        else if (h->order == MORE) t1 = newSVnv(-FKEY(NV, h, 1));
        else croak("No fast %s order", order_name(h));

        while (l < n) {
            key1 = FKEY(NV, h, l);
            key2 = FKEY(NV, h, l+1);
            if (key1 < key) {
                if (key2 < key1) {
                    FKEY(NV, h, l/2) = key2;
                    l++;
                } else {
                    FKEY(NV, h, l/2) = key1;
                }
            } else if (key2 < key) {
                FKEY(NV, h, l/2) = key2;
                l++;
            } else break;
            if (h->has_values) h->values[l/2] = h->values[l];
            l *= 2;
        }
        if (l == n) {
            key1 = FKEY(NV, h, l);
            if (key1 < key) {
                FKEY(NV, h, l/2) = key1;
                if (h->has_values) h->values[l/2] = h->values[l];
                l*= 2;
            }
        }
        l /= 2;
        FKEY(NV, h, l) = key;
        if (h->has_values) h->values[l] = h->values[h->used];
    } else {
        SV *key, *key1, *key2;

        key = KEY(h, h->used-1);
        while (l < n) {
            key1 = KEY(h, l);
            if (MAGIC && SvGMAGICAL(key1)) key1 = sv_mortalcopy(key1);
            key2 = KEY(h, l+1);
            if (less(aTHX_ h, key1, key)) {
                if (less(aTHX_  h, key2, key1)) l++;
            } else if (less(aTHX_ h, key2, key)) l++;
            else break;
            l *= 2;
        }
        if (l == n) {
            key1 = KEY(h, l);
            if (less(aTHX_ h, key1, key)) l*= 2;
        }
        l /= 2;

        t1 = h->values[--h->used];
        if (h->wrapped) {
            key1 = h->keys[h->used];
            while (l >= 1) {
                key2 = h->keys[l];
                t2 = h->values[l];
                h->keys[l] = key1;
                h->values[l] = t1;
                key1 = key2;
                t1 = t2;
                l /= 2;
            }
            SvREFCNT_dec(key1);
        } else {
            while (l >= 1) {
                t2 = h->values[l];
                h->values[l] = t1;
                t1 = t2;
                l /= 2;
            }
        }
    }
    return t1;
}

MODULE = Heap::Simple::XS		PACKAGE = Heap::Simple::XS
PROTOTYPES: ENABLE

SV *
new(char *class, ...)
  PREINIT:
    heap h;
    UV i;
  CODE:
    if (items % 2 == 0) croak("Odd number of elements in options");
    New(__LINE__, h, 1, struct heap);
    h->keys = h->values = NULL;
    h->hkey = h->infinity = h->user_data = h->order_sv = NULL;
    h->allocated = 0;
    h->used = 1;
    h->wrapped = 0;
    h->order = 0;
    h->elements = 0;
    h->fast = 0;
    h->has_values = 1;
    h->can_die = 0;
    h->max_count = -1;
    h->dirty = 0;
    h->locked = 0;
    RETVAL = sv_newmortal();
    sv_setref_pv(RETVAL, class, (void*) h);
    for (i=1; i<items; i++) {
        STRLEN len;
        /* SvPV does magic fetch */
        char *name = SvPV(ST(i), len);
        if (len < 5) croak("Unknown option '%"SVf"'", ST(i));
        switch(name[0]) {
          case 'c':
            if (len == 7 && strEQ(name, "can_die")) {
                i++;
                /* SvTRUE does mg_get (through sv_2bool) */
                h->can_die = SvTRUE(ST(i));
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          case 'd':
            if (len == 5 && strEQ(name, "dirty")) {
                i++;
                if (h->dirty) croak("Multiple dirty options");
                /* SvTRUE does mg_get (through sv_2bool) */
                h->dirty = SvTRUE(ST(i)) ? 1 : -1;
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          case 'e':
            if (len == 8 && strEQ(name, "elements")) {
                if (h->elements) croak("Multiple elements options");
                i++;
                if (MAGIC) SvGETMAGIC(ST(i));
                if (SvROK(ST(i))) {
                    /* Some sort of reference */
                    AV *av;
                    SV **fetched;

                    av = (AV*) SvRV(ST(i));
                    if (SvTYPE(av) != SVt_PVAV)
                        croak("option elements is not an array reference");
                    fetched = av_fetch(av, 0, 0);
                    /* SvPV will do get magic */
                    if (fetched) name = SvPV(*fetched, len);
                    if (!fetched || !SvOK(*fetched))
                        croak("option elements has no type defined at index 0");
                    if (len == 6 && low_eq(name, "scalar") ||
                        len == 3 && low_eq(name, "key")) {
                        if (av_len(av) > 0)
                            warn("Extra arguments to Scalar ignored");
                        h->elements = SCALAR;
                    } else if (len == 5 && low_eq(name, "array")) {
                        h->elements = ARRAY;
                        if (av_len(av) > 0) {
                            SV **pindex, *index;
                            IV i;
                            if (av_len(av) > 1) warn("Extra arguments to Array ignored");
                            pindex = av_fetch(av, 1, 0);
                            /* SvIV will do get magic (through sv_2iv) */
                            index = pindex ? *pindex : &PL_sv_undef;
                            h->aindex = i = SvIV(index);
                            if (i != h->aindex)
                                croak("Index overflow of %"IVdf, i);
                        } else h->aindex = 0;
                    } else if (len == 4 && low_eq(name, "hash")) {
                        SV **index;
                        h->elements = HASH;
                        if (av_len(av) < 1)
                            croak("missing key name for %"SVf, *fetched);
                        if (av_len(av) > 1)
                            warn("Extra arguments to Hash ignored");
                        index = av_fetch(av, 1, 0);
                        if (h->hkey)
                            croak("Assertion: already have a hash key");
                        /* newSVsv will do get magic */
                        if (index) h->hkey = newSVsv(*index);
                        if (!index || !SvOK(*index))
                            croak("missing key name for %"SVf, *fetched);
                        h->aindex = 0;
                    } else if (len == 6 && (low_eq(name, "method") ||
                                            low_eq(name, "object"))) {
                        SV **index;
                        if (toLOWER(name[0]) == 'm') {
                            h->elements = METHOD;
                            if (av_len(av) < 1)
                                croak("missing key method for %"SVf, *fetched);
                        } else {
                            h->elements = OBJECT;
                            h->wrapped  = 1;
                            if (av_len(av) < 1) break;
                        }
                        if (av_len(av) > 1)
                            warn("Extra arguments to %"SVf" ignored", *fetched);
                        index = av_fetch(av, 1, 0);
                        if (h->hkey)
                            croak("Assertion: already have a method name");
                        /* newSVsv will do get magic */
                        if (index) h->hkey = newSVsv(*index);
                        if (!index || !SvOK(*index))
                            croak("missing key method for %"SVf, *fetched);
                    } else if (len == 8 && low_eq(name, "function") ||
                               len == 3 && low_eq(name, "any")) {
                        SV **index;
                        if (toLOWER(name[0]) == 'f') {
                            h->elements = FUNCTION;
                            if (av_len(av) < 1)
                                croak("missing key function for %"SVf, *fetched);
                        } else {
                            h->elements = ANY_ELEM;
                            h->wrapped  = 1;
                            if (av_len(av) < 1) break;
                        }
                        if (av_len(av) > 1)
                            warn("Extra arguments to %"SVf" ignored", *fetched);
                        index = av_fetch(av, 1, 0);
                        if (h->hkey)
                            croak("Assertion: already have a key function");
                        /* Don't check if it's actually a code ref.
                           Allow unstrict name based call, or garbage that
                           never gets used */
                        /* newSVsv will do get magic */
                        if (index) h->hkey = newSVsv(*index);
                        if (!index || !SvOK(*index))
                            croak("missing key function for %"SVf, *fetched);
                    } else
                        croak("Unknown element type '%"SVf"'", *fetched);
                } else {
                    name = SvPV(ST(i), len);
                    if      (len == 6 && low_eq(name, "scalar") ||
                             len == 3 && low_eq(name, "key"))
                        h->elements = SCALAR;
                    else if (len == 5 && low_eq(name, "array")) {
                        h->elements = ARRAY;
                        h->aindex = 0;
                    } else if (len == 6 && low_eq(name, "object")) {
                        h->elements = OBJECT;
                        h->wrapped  = 1;
                    } else if (len == 3 && low_eq(name, "any")) {
                        h->elements = ANY_ELEM;
                        h->wrapped  = 1;
                    } else if (len == 4 && low_eq(name, "hash"))
                      croak("missing key name for %"SVf, ST(i));
                    else if(len == 6 && low_eq(name, "method"))
                      croak("missing key method for %"SVf, ST(i));
                    else if (len == 8 && low_eq(name, "function"))
                        croak("missing key function for %"SVf, ST(i));
                    else croak("Unknown element type '%"SVf"'", ST(i));
                }
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          case 'i':
            if (len == 8 && strEQ(name, "infinity")) {
                if (h->infinity) croak("Multiple infinity options");
                i++;
                h->infinity = newSVsv(ST(i));
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          case 'm':
            if (len == 9 && strEQ(name, "max_count")) {
                NV max_count;
                UV m;
                if (h->max_count != (UV) -1) 
                    croak("Multiple max_count options");
                i++;
                max_count = SvNV(ST(i));
                if (max_count < 0) 
                    croak("max_count should not be negative");
                if (max_count == NV_MAX*NV_MAX) break;
                if (max_count >= (UV) -1)
                    croak("max_count too big. Use infinity instead");
                m = max_count;
                if (m != max_count) 
                    croak("max_count should be an integer");
                h->max_count = m;
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          case 'o':
            if (len == 5 && strEQ(name, "order")) {
                if (h->order) croak("Multiple order options");
                i++;
                /* SvPV does get magic */
                name = SvPV(ST(i), len);
                if (SvROK(ST(i))) {
                    /* Some sort of reference */
                    SV *cv = SvRV(ST(i));
                    if (SvTYPE(cv) != SVt_PVCV)
                        croak("order value is a reference but not a code reference");
                    h->order = CODE_ORDER;
                    h->order_sv = newRV_inc(cv);
                    break;
                }
                if      (len == 1 && name[0] == '<') h->order = LESS;
                else if (len == 1 && name[0] == '>') h->order = MORE;
                else if (len == 2 && low_eq(name, "lt")) h->order = LT;
                else if (len == 2 && low_eq(name, "gt")) h->order = GT;
                else croak("Unknown order '%"SVf"'", ST(i));
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          case 'u':
            if (len == 9 && strEQ(name, "user_data")) {
                if (h->user_data) croak("Multiple user_data options");
                i++;
                h->user_data = newSVsv(ST(i));
                break;
            }
            croak("Unknown option %"SVf, ST(i));
          default:
            croak("Unknown option %"SVf, ST(i));
        }
    }
    if (!h->order) h->order    = LESS;
    if (!h->infinity) switch(h->order) {
      case LESS: h->infinity = newSVnv( NV_MAX*NV_MAX); break;
      case MORE: h->infinity = newSVnv(-NV_MAX*NV_MAX); break;
      case GT:   h->infinity = newSVpvn("", 0);         break;
      case LT: case CODE_ORDER: break;
      default:
        croak("Assertion: No infinity handler for order '%s'", 
              order_name(h));
    }
    if (!h->elements) h->elements = SCALAR;
    if (h->dirty < 0) h->dirty = 0;

    /*
       if (h->dirty && (h->order == LESS || h->order == MORE) && 
       (h->elements == SCALAR || h->wrapped)) h->fast = 1; */
    if (h->dirty && (h->order == LESS || h->order == MORE) && 
        (h->elements != FUNCTION && h->elements != METHOD)) h->fast = 1;
    if (h->fast && h->order != LESS && h->order != MORE)
        croak("No fast %s order", order_name(h));
    if (h->fast && h->elements == SCALAR) h->has_values = 0;
    h->key_ops = h->wrapped || (h->fast && h->has_values);
    /* Can't happen, but let's just make sure */
    if (h->wrapped && !h->has_values) 
        croak("Assertion: wrapped but no has_values");
    SvREFCNT_inc(RETVAL);
  OUTPUT:
    RETVAL

UV
count(heap h)
  CODE:
    RETVAL = h->used-1;
  OUTPUT:
    RETVAL

void
insert(heap h, SV *value)
  PPCODE:
    if (h->locked) croak("recursive heap change");
    SAVEINT(h->locked);
    h->locked = 1;
    PUTBACK;
    key_insert(aTHX_ h, NULL, value);

void
key_insert(heap h, SV *key, SV *value)
  PPCODE:
    if (!h->key_ops) croak("This heap type does not support key_insert");
    if (h->locked) croak("recursive heap change");
    SAVEINT(h->locked);
    h->locked = 1;
    PUTBACK;
    key_insert(aTHX_ h, key, value);

void
_key_insert(heap h, SV *pair)
  PREINIT:
    AV *av;
    SV **key, **value;
  PPCODE:
    if (!h->key_ops) croak("This heap type does not support _key_insert");
    if (MAGIC) SvGETMAGIC(pair);
    if (!SvROK(pair)) croak("pair is not a reference");
    av = (AV*) SvRV(pair);
    if (SvTYPE(av) != SVt_PVAV) croak("pair is not an ARRAY reference");
    key = av_fetch(av, 0, 0);
    if (!key) croak("No key in the element array");
    value = av_fetch(av, 1, 0);
    if (!value) croak("No value in the element array");
    if (h->locked) croak("recursive heap change");
    SAVEINT(h->locked);
    h->locked = 1;
    PUTBACK;
    key_insert(aTHX_ h, *key, *value);

void
extract_top(heap h)
  ALIAS:
    Heap::Simple::XS::extract_min   = 1
    Heap::Simple::XS::extract_first = 2
  PPCODE:
    if (h->used <= 2) {
        if (h->used < 2) {
            if (ix != 2) croak("Empty heap");
            XSRETURN_EMPTY;
        }
        if (h->locked) croak("recursive heap change");
        SAVEINT(h->locked);
        h->locked = 1;
        --h->used;
        if (h->wrapped && !h->fast) SvREFCNT_dec(h->keys[h->used]);
        if (h->has_values) PUSHs(sv_2mortal(h->values[h->used]));
        else if (h->order == LESS) XSRETURN_NV( FKEY(NV, h, 1));
        else if (h->order == MORE) XSRETURN_NV(-FKEY(NV, h, 1));
        else croak("No fast %s order", order_name(h));
    } else {
        PUTBACK;
        if (h->locked) croak("recursive heap change");
        SAVEINT(h->locked);
        h->locked = 1;
        PUSHs(sv_2mortal(extract_top(aTHX_ h)));
    }

void
extract_upto(heap h, SV *border)
  PPCODE:
    /* special case, avoid uneeded access to border */
    if (h->used < 2) return;
    if (h->locked) croak("recursive heap change");
    SAVEINT(h->locked);
    h->locked = 1;
    if (h->fast) {
        NV b;
        if      (h->order == LESS) b =  SvNV(border);
        else if (h->order == MORE) b = -SvNV(border);
        else croak("No fast %s order", order_name(h));
        while (FKEY(NV, h, 1) <= b) {
            /* No PUTBACK/SPAGAIN needed since fast extract top 
               won't change the stack */
            XPUSHs(sv_2mortal(extract_top(aTHX_ h)));
            if (h->used < 2) break;
        }
    } else {
        if (MAGIC && SvGMAGICAL(border)) border = sv_mortalcopy(border);
        while (1) {
            PUTBACK;
            if (less(aTHX_ h, border, KEY(h, 1))) {
                SPAGAIN;
                break;
            }
            SPAGAIN;
            XPUSHs(sv_2mortal(extract_top(aTHX_ h)));
            if (h->used < 2) break;
        }
    }
    if ((h->used+4)*4 < h->allocated) extend(h); /* shrink really */

void
top(heap h)
  ALIAS:
    Heap::Simple::XS::first = 1
  PPCODE:
    if (h->used < 2) {
        if (ix != 1) croak("Empty heap");
        XSRETURN_EMPTY;
    }
    if (h->has_values) PUSHs(sv_2mortal(SvREFCNT_inc(h->values[1])));
    else if (h->order == LESS) XSRETURN_NV( FKEY(NV, h, 1));
    else if (h->order == MORE) XSRETURN_NV(-FKEY(NV, h, 1));
    else croak("No fast %s order", order_name(h));

void
top_key(heap h)
  ALIAS:
    Heap::Simple::XS::min_key   = 1
    Heap::Simple::XS::first_key = 2
  PPCODE:
    if (h->used < 2) {
        if (ix == 2) XSRETURN_EMPTY;
        if (!h->infinity || !SvOK(h->infinity)) croak("Empty heap");
        PUSHs(sv_2mortal(SvREFCNT_inc(h->infinity)));
    } else if (h->fast) {
        if      (h->order== LESS) XSRETURN_NV( FKEY(NV, h, 1));
        else if (h->order== MORE) XSRETURN_NV(-FKEY(NV, h, 1));
        else croak("No fast %s order", order_name(h));
    } else PUSHs(sv_2mortal(SvREFCNT_inc(KEY(h, 1))));

void
keys(heap h)
  PREINIT:
    /* you can actally modify the values through the return */
    UV i;
    SV *key;
  PPCODE:
    EXTEND(SP, h->used-1);
    if (h->fast) {
        if      (h->order == LESS) for (i=1; i<h->used; i++)
            PUSHs(sv_2mortal(newSVnv( FKEY(NV, h, i))));
        else if (h->order == MORE) for (i=1; i<h->used; i++)
            PUSHs(sv_2mortal(newSVnv(-FKEY(NV, h, i))));
        else croak("No fast %s order", order_name(h));
    } else {
        for (i=1; i<h->used; i++) {
            PUTBACK;
            key = KEY(h, i);
            SPAGAIN;
            PUSHs(sv_2mortal(SvREFCNT_inc(key)));
        }
    }

void
values(heap h)
  PREINIT:
    /* you can actally modify the values through the return */
    UV i;
  PPCODE:
    EXTEND(SP, h->used-1);
    if (h->has_values) for (i=1; i<h->used; i++)
        PUSHs(sv_2mortal(SvREFCNT_inc(h->values[i])));
    else if (h->order == LESS) for (i=1; i<h->used; i++)
        PUSHs(sv_2mortal(newSVnv( FKEY(NV, h, i))));
    else if (h->order == MORE) for (i=1; i<h->used; i++)
        PUSHs(sv_2mortal(newSVnv(-FKEY(NV, h, i))));
    else croak("No fast %s order", order_name(h));

void
clear(heap h)
  PREINIT:
    SV *key, *value;
  PPCODE:
    if (h->locked) croak("recursive heap change");
    SAVEINT(h->locked);
    h->locked = 1;
    if (h->fast || !h->wrapped) {
        if (h->has_values)
            while (h->used > 1) SvREFCNT_dec(h->values[--h->used]);
        else h->used = 1;
    } else {
        while (h->used > 1) {
            --h->used;
            value = h->values[h->used];
            key   = h->keys  [h->used];
            SvREFCNT_dec(key);
            SvREFCNT_dec(value);
        }
    }
    if ((h->used+4)*4 < h->allocated) extend(h); /* shrink really */

SV *
key(heap h, SV *value)
  CODE:
    if (h->fast) {
        RETVAL = newSVnv(SvNV(fetch_key(h, value)));
    } else {
        RETVAL = SvREFCNT_inc(fetch_key(h, value));
    }

  OUTPUT:
    RETVAL

void
_absorb(SV * heap1, SV *heap2)
  PREINIT:
    int copied2;
    SV *heap1_ref, *value;
    IV tmp;
    heap h1;
  PPCODE:
    /* Helper for absorb, puts h1 into h2 */
    if (sv_derived_from(heap1, "Heap::Simple::XS")) {
        heap1_ref = (SV*) SvRV(heap1);
        tmp = SvIV(heap1_ref);
        h1 = INT2PTR(heap, tmp);
    } else if (!SvOK(heap1)) croak("h1 is undefined");
    else croak("h1 is not of type Heap::Simple::XS");
    if (h1->used < 2) XSRETURN_EMPTY;
    if (h1->locked) croak("recursive heap change");
    SAVEINT(h1->locked);
    h1->locked = 1;

    if (MAGIC && SvMAGICAL(heap2)) {
        heap2 = sv_mortalcopy(heap2);
        copied2 = 1;
    } else copied2 = 0;
    /* If we are an XS heap, the argument probably is too */
    if (sv_derived_from(heap2, "Heap::Simple::XS")) {
        heap h2;
        SV *heap2_ref;

        heap2_ref = (SV*) SvRV(heap2);
        tmp = SvIV(heap2_ref);
        h2 = INT2PTR(heap, tmp);
        if (h1 == h2) croak("Self absorption");

        /* Keep arguments alive for the duration */
        sv_2mortal(SvREFCNT_inc(heap1_ref));
        if (!copied2) sv_2mortal(SvREFCNT_inc(heap2_ref));

        if (h1->fast) value = sv_newmortal();
        while (h1->used >= 2) {
            SAVETMPS;
            if (h1->has_values) value = h1->values[h1->used-1];
            else if (h1->order == LESS) 
                sv_setnv(value, FKEY(NV, h1, h1->used-1));
            else if (h1->order == MORE) 
                sv_setnv(value, -FKEY(NV, h1, h1->used-1));
            else croak("No fast %s order", order_name(h1));

            key_insert(h2, NULL, value);

            h1->used--;
            if (h1->has_values) SvREFCNT_dec(value);
            if (h1->wrapped && !h1->fast) SvREFCNT_dec(h1->keys[h1->used]);
            if ((h1->used+4)*4 < h1->allocated) extend(h1); /* shrink really */
            FREETMPS;
        }
    } else if (!SvOK(heap2)) croak("heap2 is undefined");
    else if (!sv_isobject(heap2)) croak("heap2 is not an object reference");
    else {
        I32 count;
        int wrapped;

        ENTER;
        /* Simple way to keep the refcount up at both levels */
        if (!copied2) heap2 = sv_mortalcopy(heap2);
        if (h1->fast) value = sv_newmortal();
        while (h1->used >= 2) {
            SAVETMPS;
            if (h1->has_values) value = h1->values[h1->used-1];
            else if (h1->order == LESS) 
                sv_setnv(value,  FKEY(NV, h1, h1->used-1));
            else if (h1->order == MORE) 
                sv_setnv(value, -FKEY(NV, h1, h1->used-1));
            else croak("No fast %s order", order_name(h1));
            PUSHMARK(SP);
            PUSHs(heap2);
            PUSHs(value);
            PUTBACK;

            count = call_method("insert", G_VOID);

            SPAGAIN;
            if (count) {
                if (count < 0) croak("Forced void context call 'insert' succeeded in returning %d values. This is impossible", (int) count);
                SP -= count;
            }
            h1->used--;
            if (h1->has_values) SvREFCNT_dec(value);
            if (h1->wrapped && !h1->fast) SvREFCNT_dec(h1->keys[h1->used]);
            if ((h1->used+4)*4 < h1->allocated) extend(h1); /* shrink really */
            FREETMPS;
        }
        LEAVE;
    }

void
_key_absorb(SV * heap1, SV *heap2)
  PREINIT:
    int copied2;
    SV *heap1_ref, *key, *value;
    IV tmp;
    heap h1;
  PPCODE:
    /* Helper for absorb, puts h1 into h2 */
    if (sv_derived_from(heap1, "Heap::Simple::XS")) {
        heap1_ref = (SV*) SvRV(heap1);
        tmp = SvIV(heap1_ref);
        h1 = INT2PTR(heap, tmp);
    } else if (!SvOK(heap1)) croak("h1 is undefined");
    else croak("h1 is not of type Heap::Simple::XS");
    if (h1->used < 2) XSRETURN_EMPTY;
    if (h1->locked) croak("recursive heap change");
    SAVEINT(h1->locked);
    h1->locked = 1;

    if (MAGIC && SvMAGICAL(heap2)) {
        heap2 = sv_mortalcopy(heap2);
        copied2 = 1;
    } else copied2 = 0;
    /* If we are an XS heap, the argument probably is too */
    if (sv_derived_from(heap2, "Heap::Simple::XS")) {
        heap h2;
        SV *heap2_ref;

        heap2_ref = (SV*) SvRV(heap2);
        tmp = SvIV(heap2_ref);
        h2 = INT2PTR(heap, tmp);
        if (h1 == h2) croak("Self absorption");
        if (!h2->key_ops) croak("This heap type does not support key_insert");

        /* Keep arguments alive for the duration */
        sv_2mortal(SvREFCNT_inc(heap1_ref));
        if (!copied2) sv_2mortal(SvREFCNT_inc(heap2_ref));

        if (h1->fast)        key   = sv_newmortal();
        if (!h1->has_values) value = sv_newmortal();
        while (h1->used >= 2) {
            SAVETMPS;
            if (h1->has_values) value = h1->values[h1->used-1];
            else if (h1->order == LESS) 
                sv_setnv(value, FKEY(NV, h1, h1->used-1));
            else if (h1->order == MORE) 
                sv_setnv(value, -FKEY(NV, h1, h1->used-1));
            else croak("No fast %s order", order_name(h1));

            if (!h1->fast) key = KEY(h1, h1->used-1);
            else if (h1->order== LESS) 
                sv_setnv(key,  FKEY(NV, h1, h1->used-1));
            else if (h1->order== MORE) 
                sv_setnv(key, -FKEY(NV, h1, h1->used-1));
            else croak("No fast %s order", order_name(h1));

            key_insert(h2, key, value);

            h1->used--;
            if (h1->has_values) SvREFCNT_dec(value);
            if (h1->wrapped && !h1->fast) SvREFCNT_dec(h1->keys[h1->used]);
            if ((h1->used+4)*4 < h1->allocated) extend(h1); /* shrink really */
            FREETMPS;
        }
    } else if (!SvOK(heap2)) croak("heap2 is undefined");
    else if (!sv_isobject(heap2)) croak("heap2 is not an object reference");
    else {
        I32 count;
        int wrapped;

        ENTER;
        /* We will push up to three arguments */
        EXTEND(SP, 3);
        /* Simple way to keep the refcount up at both levels */
        if (!copied2) heap2 = sv_mortalcopy(heap2);

        if (h1->fast)        key   = sv_newmortal();
        if (!h1->has_values) value = sv_newmortal();
        while (h1->used >= 2) {
            SAVETMPS;
            if (h1->has_values) value = h1->values[h1->used-1];
            else if (h1->order == LESS) 
                sv_setnv(value,  FKEY(NV, h1, h1->used-1));
            else if (h1->order == MORE) 
                sv_setnv(value, -FKEY(NV, h1, h1->used-1));
            else croak("No fast %s order", order_name(h1));

            if (!h1->fast) key = KEY(h1, h1->used-1);
            else if (h1->order== LESS) 
                sv_setnv(key,  FKEY(NV, h1, h1->used-1));
            else if (h1->order== MORE) 
                sv_setnv(key, -FKEY(NV, h1, h1->used-1));
            else croak("No fast %s order", order_name(h1));

            PUSHMARK(SP);
            PUSHs(heap2);
            PUSHs(key);
            PUSHs(value);
            PUTBACK;

            count = call_method("key_insert", G_VOID);

            SPAGAIN;
            if (count) {
                if (count < 0) croak("Forced void context call 'key_insert' succeeded in returning %d values. This is impossible", (int) count);
                SP -= count;
            }
            h1->used--;
            if (h1->has_values) SvREFCNT_dec(value);
            if (h1->wrapped && !h1->fast) SvREFCNT_dec(h1->keys[h1->used]);
            if ((h1->used+4)*4 < h1->allocated) extend(h1); /* shrink really */
            FREETMPS;
        }
        LEAVE;
    }

void
absorb(SV *heap1, SV *heap2)
  PREINIT:
    I32 count;
  PPCODE:
    if (MAGIC && SvMAGICAL(heap2)) heap2 = sv_mortalcopy(heap2);
    PUSHMARK(SP);
    PUSHs(heap2);
    PUSHs(heap1);
    PUTBACK;
    count = call_method("_absorb", G_VOID);
    /* Needed or the stack will remember and return the stuff we pushed */
    SPAGAIN;
    if (count) {
        if (count < 0) croak("Forced void context call '_absorb' succeeded in returning %d values. This is impossible", (int) count);
        SP -= count;
    }

void
key_absorb(SV *heap1, SV *heap2)
  PREINIT:
    I32 count;
  PPCODE:
    if (MAGIC && SvMAGICAL(heap2)) heap2 = sv_mortalcopy(heap2);
    PUSHMARK(SP);
    PUSHs(heap2);
    PUSHs(heap1);
    PUTBACK;
    count = call_method("_key_absorb", G_VOID);
    /* Needed or the stack will remember and return the stuff we pushed */
    SPAGAIN;
    if (count) {
        if (count < 0) croak("Forced void context call '_key_absorb' succeeded in returning %d values. This is impossible", (int) count);
        SP -= count;
    }

void
infinity(heap h, SV *new_infinity=0)
  PPCODE:
    if (GIMME_V != G_VOID)
        XPUSHs(h->infinity ?
               sv_2mortal(SvREFCNT_inc(h->infinity)) : &PL_sv_undef);
    if (new_infinity) {
        if (h->infinity) sv_2mortal(h->infinity);
        h->infinity = newSVsv(new_infinity);
    }

IV
key_index(heap h)
  CODE:
    if (h->elements != ARRAY) croak("Heap elements are not of type 'Array'");
    RETVAL = h->aindex;
  OUTPUT:
    RETVAL

SV *
key_name(heap h)
  CODE:
    if (h->elements != HASH) croak("Heap elements are not of type 'Hash'");
    /* Make a copy instead of returning an lvalue
       so that the cached aindex remains valid */
    RETVAL = newSVsv(h->hkey);
  OUTPUT:
    RETVAL

SV *
key_method(heap h)
  CODE:
    if (h->elements != METHOD && h->elements != OBJECT)
        croak("Heap elements are not of type 'Method' or 'Object'");
    RETVAL = SvREFCNT_inc(h->hkey);
  OUTPUT:
    RETVAL

SV *
key_function(heap h)
  CODE:
    if (h->elements != FUNCTION && h->elements != ANY_ELEM)
        croak("Heap elements are not of type 'Function' or 'Any'");
    RETVAL = SvREFCNT_inc(h->hkey);
  OUTPUT:
    RETVAL

void
user_data(heap h, SV *new_user_data=0)
  PPCODE:
    if (GIMME_V != G_VOID)
        XPUSHs(h->user_data ?
               sv_2mortal(SvREFCNT_inc(h->user_data)) : &PL_sv_undef);
    if (new_user_data) {
        if (h->user_data) sv_2mortal(h->user_data);
        h->user_data = newSVsv(new_user_data);
    }

SV *
order(heap h)
  CODE:
    if (h->order == CODE_ORDER) RETVAL = SvREFCNT_inc(h->order_sv);
    else                        RETVAL = newSVpv(order_name(h), 0);
  OUTPUT:
    RETVAL

void
elements(heap h)
  PPCODE:
    XPUSHs(sv_2mortal(newSVpv(elements_name(h), 0)));
    if (GIMME_V == G_ARRAY) switch(h->elements) {
      case SCALAR:
        break;
      case ARRAY:
        XPUSHs(sv_2mortal(newSViv(h->aindex)));
        break;
      case HASH:
      case METHOD:
      case OBJECT:
      case FUNCTION:
      case ANY_ELEM:
        if (h->hkey) XPUSHs(sv_2mortal(newSVsv(h->hkey)));
        break;
      default:
        croak("Assertion: unhandled element type %s", elements_name(h));
    }

void
wrapped(heap h)
  PPCODE:
    if (h->key_ops) XSRETURN_YES;
    if (GIMME_V == G_SCALAR) XSRETURN_NO;
    XSRETURN_EMPTY;

void
dirty(heap h)
  PPCODE:
    if (h->dirty) XSRETURN_YES;
    if (GIMME_V == G_SCALAR) XSRETURN_NO;
    XSRETURN_EMPTY;

void
can_die(heap h)
  PPCODE:
    /* ->fast types are wrapped too really */
    if (h->can_die) XSRETURN_YES;
    if (GIMME_V == G_SCALAR) XSRETURN_NO;
    XSRETURN_EMPTY;

void
max_count(heap h)
  PPCODE:
    if (h->max_count == (UV) -1) XSRETURN_NV(NV_MAX*NV_MAX);
    XSRETURN_UV(h->max_count);

void
DESTROY(heap h)
  PREINIT:
    SV *key, *value;
  PPCODE:
    if (h->locked) warn("lock during DESTROY. Something is *deeply* wrong");
    if (h->fast || !h->wrapped) {
        if (h->has_values)
            while (h->used > 1) SvREFCNT_dec(h->values[--h->used]);
    } else {
        while (h->used > 1) {
            --h->used;
            value = h->values[h->used];
            key   = h->keys  [h->used];
            SvREFCNT_dec(key);
            SvREFCNT_dec(value);
        }
    }
    if (h->hkey) {
        key = h->hkey;
        h->hkey = NULL;
        SvREFCNT_dec(key);
    }
    if (h->infinity) {
        key = h->infinity;
        h->infinity = NULL;
        SvREFCNT_dec(key);
    }
    if (h->user_data) {
        key = h->user_data;
        h->user_data = NULL;
        SvREFCNT_dec(key);
    }
    if (h->order_sv) {
        key = h->order_sv;
        h->order_sv = NULL;
        SvREFCNT_dec(key);
    }
    if (h->values) Safefree(h->values);
    if (h->keys)   Safefree(h->keys);
    Safefree(h);
