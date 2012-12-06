/*
 * Copyright (c) 1991-1994 by Xerox Corporation.  All rights reserved.
 * opyright (c) 1999-2000 by Hewlett-Packard Company.  All rights reserved.
 *
 * THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
 * OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
 *
 * Permission is hereby granted to use or copy this program
 * for any purpose,  provided the above notices are retained on all copies.
 * Permission to modify the code and to distribute modified code is granted,
 * provided the above notices are retained, and a notice that the code was
 * modified is included with the above copyright notice.
 *
 */

#include "private/gc_pmark.h"

/*
 * Some simple primitives for allocation with explicit type information.
 * Simple objects are allocated such that they contain a GC_descr at the
 * end (in the last allocated word).  This descriptor may be a procedure
 * which then examines an extended descriptor passed as its environment.
 *
 * Arrays are treated as simple objects if they have sufficiently simple
 * structure.  Otherwise they are allocated from an array kind that supplies
 * a special mark procedure.  These arrays contain a pointer to a
 * complex_descriptor as their last word.
 * This is done because the environment field is too small, and the collector
 * must trace the complex_descriptor.
 *
 * Note that descriptors inside objects may appear cleared, if we encounter a
 * false reference to an object on a free list.  In the GC_descr case, this
 * is OK, since a 0 descriptor corresponds to examining no fields.
 * In the complex_descriptor case, we explicitly check for that case.
 *
 * MAJOR PARTS OF THIS CODE HAVE NOT BEEN TESTED AT ALL and are not testable,
 * since they are not accessible through the current interface.
 */

#include "gc_typed.h"

#define TYPD_EXTRA_BYTES (sizeof(word) - EXTRA_BYTES)

STATIC GC_bool GC_explicit_typing_initialized = FALSE;

STATIC int GC_explicit_kind = 0;
                        /* Object kind for objects with indirect        */
                        /* (possibly extended) descriptors.             */

STATIC int GC_array_kind = 0;
                        /* Object kind for objects with complex         */
                        /* descriptors and GC_array_mark_proc.          */

/* Extended descriptors.  GC_typed_mark_proc understands these. */
/* These are used for simple objects that are larger than what  */
/* can be described by a BITMAP_BITS sized bitmap.              */
typedef struct {
        word ed_bitmap; /* lsb corresponds to first word.       */
        GC_bool ed_continued;   /* next entry is continuation.  */
} ext_descr;

/* Array descriptors.  GC_array_mark_proc understands these.    */
/* We may eventually need to add provisions for headers and     */
/* trailers.  Hence we provide for tree structured descriptors, */
/* though we don't really use them currently.                   */
typedef union ComplexDescriptor {
    struct LeafDescriptor {     /* Describes simple array       */
        word ld_tag;
#       define LEAF_TAG 1
        size_t ld_size;         /* bytes per element    */
                                /* multiple of ALIGNMENT        */
        size_t ld_nelements;    /* Number of elements.  */
        GC_descr ld_descriptor; /* A simple length, bitmap,     */
                                /* or procedure descriptor.     */
    } ld;
    struct ComplexArrayDescriptor {
        word ad_tag;
#       define ARRAY_TAG 2
        size_t ad_nelements;
        union ComplexDescriptor * ad_element_descr;
    } ad;
    struct SequenceDescriptor {
        word sd_tag;
#       define SEQUENCE_TAG 3
        union ComplexDescriptor * sd_first;
        union ComplexDescriptor * sd_second;
    } sd;
} complex_descriptor;
#define TAG ld.ld_tag

STATIC ext_descr * GC_ext_descriptors = NULL;
                                        /* Points to array of extended  */
                                        /* descriptors.                 */

STATIC size_t GC_ed_size = 0;   /* Current size of above arrays.        */
#define ED_INITIAL_SIZE 100

STATIC size_t GC_avail_descr = 0;       /* Next available slot.         */

STATIC int GC_typed_mark_proc_index = 0; /* Indices of my mark          */
STATIC int GC_array_mark_proc_index = 0; /* procedures.                 */

STATIC void GC_push_typed_structures_proc(void)
{
  GC_push_all((ptr_t)&GC_ext_descriptors,
              (ptr_t)&GC_ext_descriptors + sizeof(word));
}

/* Add a multiword bitmap to GC_ext_descriptors arrays.  Return */
/* starting index.                                              */
/* Returns -1 on failure.                                       */
/* Caller does not hold allocation lock.                        */
STATIC signed_word GC_add_ext_descriptor(const GC_word * bm, word nbits)
{
    size_t nwords = divWORDSZ(nbits + WORDSZ-1);
    signed_word result;
    size_t i;
    word last_part;
    size_t extra_bits;
    DCL_LOCK_STATE;

    LOCK();
    while (GC_avail_descr + nwords >= GC_ed_size) {
        ext_descr * new;
        size_t new_size;
        word ed_size = GC_ed_size;

        if (ed_size == 0) {
            GC_ASSERT((word)&GC_ext_descriptors % sizeof(word) == 0);
            GC_push_typed_structures = GC_push_typed_structures_proc;
            UNLOCK();
            new_size = ED_INITIAL_SIZE;
        } else {
            UNLOCK();
            new_size = 2 * ed_size;
            if (new_size > MAX_ENV) return(-1);
        }
        new = (ext_descr *) GC_malloc_atomic(new_size * sizeof(ext_descr));
        if (new == 0) return(-1);
        LOCK();
        if (ed_size == GC_ed_size) {
            if (GC_avail_descr != 0) {
                BCOPY(GC_ext_descriptors, new,
                      GC_avail_descr * sizeof(ext_descr));
            }
            GC_ed_size = new_size;
            GC_ext_descriptors = new;
        }  /* else another thread already resized it in the meantime */
    }
    result = GC_avail_descr;
    for (i = 0; i < nwords-1; i++) {
        GC_ext_descriptors[result + i].ed_bitmap = bm[i];
        GC_ext_descriptors[result + i].ed_continued = TRUE;
    }
    last_part = bm[i];
    /* Clear irrelevant bits. */
    extra_bits = nwords * WORDSZ - nbits;
    last_part <<= extra_bits;
    last_part >>= extra_bits;
    GC_ext_descriptors[result + i].ed_bitmap = last_part;
    GC_ext_descriptors[result + i].ed_continued = FALSE;
    GC_avail_descr += nwords;
    UNLOCK();
    return(result);
}
STATIC ptr_t * GC_eobjfreelist = NULL;

STATIC ptr_t * GC_arobjfreelist = NULL;

STATIC mse * GC_typed_mark_proc(word * addr, mse * mark_stack_ptr,
                                mse * mark_stack_limit, word env);

STATIC mse * GC_array_mark_proc(word * addr, mse * mark_stack_ptr,
                                mse * mark_stack_limit, word env);

/* Caller does not hold allocation lock. */
GC_API void GC_CALL GC_init_explicit_typing(void)
{
    DCL_LOCK_STATE;

    GC_STATIC_ASSERT(sizeof(struct LeafDescriptor) % sizeof(word) == 0);
    LOCK();
    if (GC_explicit_typing_initialized) {
      UNLOCK();
      return;
    }
    GC_explicit_typing_initialized = TRUE;
    /* Set up object kind with simple indirect descriptor. */
      GC_eobjfreelist = (ptr_t *)GC_new_free_list_inner();
      GC_explicit_kind = GC_new_kind_inner(
                            (void **)GC_eobjfreelist,
                            (WORDS_TO_BYTES((word)-1) | GC_DS_PER_OBJECT),
                            TRUE, TRUE);
                /* Descriptors are in the last word of the object. */
      GC_typed_mark_proc_index = GC_new_proc_inner(GC_typed_mark_proc);
    /* Set up object kind with array descriptor. */
      GC_arobjfreelist = (ptr_t *)GC_new_free_list_inner();
      GC_array_mark_proc_index = GC_new_proc_inner(GC_array_mark_proc);
      GC_array_kind = GC_new_kind_inner(
                            (void **)GC_arobjfreelist,
                            GC_MAKE_PROC(GC_array_mark_proc_index, 0),
                            FALSE, TRUE);
    UNLOCK();
}

STATIC mse * GC_typed_mark_proc(word * addr, mse * mark_stack_ptr,
                                mse * mark_stack_limit, word env)
{
    word bm = GC_ext_descriptors[env].ed_bitmap;
    word * current_p = addr;
    word current;
    ptr_t greatest_ha = GC_greatest_plausible_heap_addr;
    ptr_t least_ha = GC_least_plausible_heap_addr;
    DECLARE_HDR_CACHE;

    INIT_HDR_CACHE;
    for (; bm != 0; bm >>= 1, current_p++) {
        if (bm & 1) {
            current = *current_p;
            FIXUP_POINTER(current);
            if (current >= (word)least_ha && current <= (word)greatest_ha) {
                PUSH_CONTENTS((ptr_t)current, mark_stack_ptr,
                              mark_stack_limit, (ptr_t)current_p, exit1);
            }
        }
    }
    if (GC_ext_descriptors[env].ed_continued) {
        /* Push an entry with the rest of the descriptor back onto the  */
        /* stack.  Thus we never do too much work at once.  Note that   */
        /* we also can't overflow the mark stack unless we actually     */
        /* mark something.                                              */
        mark_stack_ptr++;
        if ((word)mark_stack_ptr >= (word)mark_stack_limit) {
            mark_stack_ptr = GC_signal_mark_stack_overflow(mark_stack_ptr);
        }
        mark_stack_ptr -> mse_start = (ptr_t)(addr + WORDSZ);
        mark_stack_ptr -> mse_descr.w =
                        GC_MAKE_PROC(GC_typed_mark_proc_index, env + 1);
    }
    return(mark_stack_ptr);
}

/* Return the size of the object described by d.  It would be faster to */
/* store this directly, or to compute it as part of                     */
/* GC_push_complex_descriptor, but hopefully it doesn't matter.         */
STATIC word GC_descr_obj_size(complex_descriptor *d)
{
    switch(d -> TAG) {
      case LEAF_TAG:
        return(d -> ld.ld_nelements * d -> ld.ld_size);
      case ARRAY_TAG:
        return(d -> ad.ad_nelements
               * GC_descr_obj_size(d -> ad.ad_element_descr));
      case SEQUENCE_TAG:
        return(GC_descr_obj_size(d -> sd.sd_first)
               + GC_descr_obj_size(d -> sd.sd_second));
      default:
        ABORT_RET("Bad complex descriptor");
        return 0;
    }
}

/* Push descriptors for the object at addr with complex descriptor d    */
/* onto the mark stack.  Return 0 if the mark stack overflowed.         */
STATIC mse * GC_push_complex_descriptor(word *addr, complex_descriptor *d,
                                        mse *msp, mse *msl)
{
    register ptr_t current = (ptr_t) addr;
    register word nelements;
    register word sz;
    register word i;

    switch(d -> TAG) {
      case LEAF_TAG:
        {
          register GC_descr descr = d -> ld.ld_descriptor;

          nelements = d -> ld.ld_nelements;
          if (msl - msp <= (ptrdiff_t)nelements) return(0);
          sz = d -> ld.ld_size;
          for (i = 0; i < nelements; i++) {
              msp++;
              msp -> mse_start = current;
              msp -> mse_descr.w = descr;
              current += sz;
          }
          return(msp);
        }
      case ARRAY_TAG:
        {
          register complex_descriptor *descr = d -> ad.ad_element_descr;

          nelements = d -> ad.ad_nelements;
          sz = GC_descr_obj_size(descr);
          for (i = 0; i < nelements; i++) {
              msp = GC_push_complex_descriptor((word *)current, descr,
                                                msp, msl);
              if (msp == 0) return(0);
              current += sz;
          }
          return(msp);
        }
      case SEQUENCE_TAG:
        {
          sz = GC_descr_obj_size(d -> sd.sd_first);
          msp = GC_push_complex_descriptor((word *)current, d -> sd.sd_first,
                                           msp, msl);
          if (msp == 0) return(0);
          current += sz;
          msp = GC_push_complex_descriptor((word *)current, d -> sd.sd_second,
                                           msp, msl);
          return(msp);
        }
      default:
        ABORT_RET("Bad complex descriptor");
        return 0;
   }
}

STATIC mse * GC_array_mark_proc(word * addr, mse * mark_stack_ptr,
                                mse * mark_stack_limit,
                                word env GC_ATTR_UNUSED)
{
    hdr * hhdr = HDR(addr);
    size_t sz = hhdr -> hb_sz;
    size_t nwords = BYTES_TO_WORDS(sz);
    complex_descriptor * descr = (complex_descriptor *)(addr[nwords-1]);
    mse * orig_mark_stack_ptr = mark_stack_ptr;
    mse * new_mark_stack_ptr;

    if (descr == 0) {
        /* Found a reference to a free list entry.  Ignore it. */
        return(orig_mark_stack_ptr);
    }
    /* In use counts were already updated when array descriptor was     */
    /* pushed.  Here we only replace it by subobject descriptors, so    */
    /* no update is necessary.                                          */
    new_mark_stack_ptr = GC_push_complex_descriptor(addr, descr,
                                                    mark_stack_ptr,
                                                    mark_stack_limit-1);
    if (new_mark_stack_ptr == 0) {
        /* Doesn't fit.  Conservatively push the whole array as a unit  */
        /* and request a mark stack expansion.                          */
        /* This cannot cause a mark stack overflow, since it replaces   */
        /* the original array entry.                                    */
        GC_mark_stack_too_small = TRUE;
        new_mark_stack_ptr = orig_mark_stack_ptr + 1;
        new_mark_stack_ptr -> mse_start = (ptr_t)addr;
        new_mark_stack_ptr -> mse_descr.w = sz | GC_DS_LENGTH;
    } else {
        /* Push descriptor itself */
        new_mark_stack_ptr++;
        new_mark_stack_ptr -> mse_start = (ptr_t)(addr + nwords - 1);
        new_mark_stack_ptr -> mse_descr.w = sizeof(word) | GC_DS_LENGTH;
    }
    return new_mark_stack_ptr;
}

GC_API GC_descr GC_CALL GC_descriptor(const GC_word * bm)
{
    GC_descr result = (GC_descr)bm;
    GC_ASSERT((result & 3) == 0);
    return result | GC_DS_BITMAP;
}

GC_API GC_descr GC_CALL GC_make_descriptor(const GC_word * bm, size_t len)
{
    signed_word last_set_bit = len - 1;
    GC_descr result;
    signed_word i;
#   define HIGH_BIT (((word)1) << (WORDSZ - 1))

    if (!EXPECT(GC_explicit_typing_initialized, TRUE))
      GC_init_explicit_typing();

    while (last_set_bit >= 0 && !GC_get_bit(bm, last_set_bit))
      last_set_bit--;
    if (last_set_bit < 0) return(0 /* no pointers */);
#   if ALIGNMENT == CPP_WORDSZ/8
    {
      register GC_bool all_bits_set = TRUE;
      for (i = 0; i < last_set_bit; i++) {
        if (!GC_get_bit(bm, i)) {
            all_bits_set = FALSE;
            break;
        }
      }
      if (all_bits_set) {
        /* An initial section contains all pointers.  Use length descriptor. */
        return (WORDS_TO_BYTES(last_set_bit+1) | GC_DS_LENGTH);
      }
    }
#   endif
    if ((word)last_set_bit < BITMAP_BITS) {
        /* Use conservative approximation because we have taken over    */
        /* GC_DS_BITMAP. With this, clients relying on the old bitmap   */
        /* behavior will still continue to work.                        */
        return (WORDS_TO_BYTES(last_set_bit+1) | GC_DS_LENGTH);
    } else {
        signed_word index;

        index = GC_add_ext_descriptor(bm, (word)last_set_bit+1);
        if (index == -1) return(WORDS_TO_BYTES(last_set_bit+1) | GC_DS_LENGTH);
                                /* Out of memory: use conservative      */
                                /* approximation.                       */
        result = GC_MAKE_PROC(GC_typed_mark_proc_index, (word)index);
        return result;
    }
}

GC_API void * GC_CALL GC_malloc_explicitly_typed(size_t lb, GC_descr d)
{
    ptr_t op;
    ptr_t * opp;
    size_t lg;
    DCL_LOCK_STATE;

    lb += TYPD_EXTRA_BYTES;
    if(SMALL_OBJ(lb)) {
        GC_DBG_COLLECT_AT_MALLOC(lb);
        lg = GC_size_map[lb];
        opp = &(GC_eobjfreelist[lg]);
        LOCK();
        op = *opp;
        if (EXPECT(0 == op, FALSE)) {
            UNLOCK();
            op = (ptr_t)GENERAL_MALLOC((word)lb, GC_explicit_kind);
            if (0 == op) return 0;
            lg = GC_size_map[lb];       /* May have been uninitialized. */
        } else {
            *opp = obj_link(op);
            obj_link(op) = 0;
            GC_bytes_allocd += GRANULES_TO_BYTES(lg);
            UNLOCK();
        }
        ((word *)op)[GRANULES_TO_WORDS(lg) - 1] = d;
   } else {
       op = (ptr_t)GENERAL_MALLOC((word)lb, GC_explicit_kind);
       if (op != NULL) {
            lg = BYTES_TO_GRANULES(GC_size(op));
            ((word *)op)[GRANULES_TO_WORDS(lg) - 1] = d;
       }
   }
   return((void *) op);
}

GC_API void * GC_CALL GC_malloc_explicitly_typed_ignore_off_page(size_t lb,
                                                                 GC_descr d)
{
    ptr_t op;
    ptr_t * opp;
    size_t lg;
    DCL_LOCK_STATE;

    lb += TYPD_EXTRA_BYTES;
    if( SMALL_OBJ(lb) ) {
        GC_DBG_COLLECT_AT_MALLOC(lb);
        lg = GC_size_map[lb];
        opp = &(GC_eobjfreelist[lg]);
        LOCK();
        op = *opp;
        if (EXPECT(0 == op, FALSE)) {
            UNLOCK();
            op = (ptr_t)GENERAL_MALLOC_IOP(lb, GC_explicit_kind);
            if (0 == op) return 0;
            lg = GC_size_map[lb];       /* May have been uninitialized. */
        } else {
            *opp = obj_link(op);
            obj_link(op) = 0;
            GC_bytes_allocd += GRANULES_TO_BYTES(lg);
            UNLOCK();
        }
        ((word *)op)[GRANULES_TO_WORDS(lg) - 1] = d;
   } else {
       op = (ptr_t)GENERAL_MALLOC_IOP(lb, GC_explicit_kind);
       if (op != NULL) {
         lg = BYTES_TO_WORDS(GC_size(op));
         ((word *)op)[GRANULES_TO_WORDS(lg) - 1] = d;
       }
   }
   return((void *) op);
}
