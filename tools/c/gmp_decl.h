/* gmp_decl.h: declarations of the GMP functions used by tools/c/redmaps.c and the holdouts' long-orbit programs, for
   systems that have libgmp.so.10 but no gmp.h.  Link with -l:libgmp.so.10. */
#include <stddef.h>
#include <stdio.h>
typedef unsigned long mp_limb_t; typedef long mp_size_t; typedef unsigned long mp_bitcnt_t;
typedef struct { int _mp_alloc; int _mp_size; mp_limb_t *_mp_d; } __mpz_struct;
typedef __mpz_struct mpz_t[1]; typedef __mpz_struct *mpz_ptr; typedef const __mpz_struct *mpz_srcptr;
#define D(n) __gmpz_##n
void D(init)(mpz_ptr); void D(set)(mpz_ptr, mpz_srcptr); void D(set_ui)(mpz_ptr, unsigned long); void D(set_si)(mpz_ptr, long);
void D(add)(mpz_ptr, mpz_srcptr, mpz_srcptr); void D(add_ui)(mpz_ptr, mpz_srcptr, unsigned long);
void D(sub)(mpz_ptr, mpz_srcptr, mpz_srcptr); void D(sub_ui)(mpz_ptr, mpz_srcptr, unsigned long);
void D(ui_sub)(mpz_ptr, unsigned long, mpz_srcptr);
void D(mul_ui)(mpz_ptr, mpz_srcptr, unsigned long); void D(mul_2exp)(mpz_ptr, mpz_srcptr, mp_bitcnt_t);
void D(neg)(mpz_ptr, mpz_srcptr); void D(swap)(mpz_ptr, mpz_ptr);
int D(cmp)(mpz_srcptr, mpz_srcptr); int D(cmp_si)(mpz_srcptr, long); int D(cmp_ui)(mpz_srcptr, unsigned long);
size_t D(sizeinbase)(mpz_srcptr, int); int D(tstbit)(mpz_srcptr, mp_bitcnt_t);
unsigned long D(fdiv_ui)(mpz_srcptr, unsigned long);
int D(set_str)(mpz_ptr, const char *, int); char *D(get_str)(char *, int, mpz_srcptr);
size_t D(out_str)(FILE *, int, mpz_srcptr); size_t D(inp_str)(mpz_ptr, FILE *, int);
#define mpz_init D(init)
#define mpz_set D(set)
#define mpz_set_ui D(set_ui)
#define mpz_set_si D(set_si)
#define mpz_add D(add)
#define mpz_add_ui D(add_ui)
#define mpz_sub D(sub)
#define mpz_sub_ui D(sub_ui)
#define mpz_ui_sub D(ui_sub)
#define mpz_mul_ui D(mul_ui)
#define mpz_mul_2exp D(mul_2exp)
#define mpz_neg D(neg)
#define mpz_swap D(swap)
#define mpz_cmp D(cmp)
#define mpz_cmp_si D(cmp_si)
#define mpz_cmp_ui D(cmp_ui)
#define mpz_sizeinbase D(sizeinbase)
#define mpz_tstbit D(tstbit)
#define mpz_fdiv_ui D(fdiv_ui)
#define mpz_set_str D(set_str)
#define mpz_get_str D(get_str)
#define mpz_out_str D(out_str)
#define mpz_inp_str D(inp_str)
#define mpz_sgn(z) ((z)->_mp_size < 0 ? -1 : (z)->_mp_size > 0)
#define mpz_odd_p(z) ((z)->_mp_size != 0 && ((z)->_mp_d[0] & 1))
void __gmpz_fdiv_q_2exp(mpz_ptr, mpz_srcptr, mp_bitcnt_t);
#define mpz_fdiv_q_2exp_(r, a) __gmpz_fdiv_q_2exp(r, a, 1)
void __gmpz_tdiv_q_ui(mpz_ptr, mpz_srcptr, unsigned long);
#define mpz_tdiv_q_ui(r, a, d) __gmpz_tdiv_q_ui(r, a, d)
mp_limb_t __gmpz_getlimbn(mpz_srcptr, mp_size_t);
#define mpz_getlimbn_(z) __gmpz_getlimbn(z, 0)
