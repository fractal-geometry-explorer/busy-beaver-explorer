/* Minimal declarations of the GMP functions used by orbit.c, for systems with libgmp.so.10 but no gmp.h.
   With gmp.h installed, compile with -DHAVE_GMP_H instead. */
#ifdef HAVE_GMP_H
#include <gmp.h>
#else
#include <stddef.h>
typedef unsigned long mp_limb_t;
typedef long mp_size_t;
typedef unsigned long mp_bitcnt_t;
typedef struct { int _mp_alloc; int _mp_size; mp_limb_t *_mp_d; } __mpz_struct;
typedef __mpz_struct mpz_t[1];
typedef __mpz_struct *mpz_ptr;
typedef const __mpz_struct *mpz_srcptr;
#define mpz_init __gmpz_init
#define mpz_clear __gmpz_clear
#define mpz_set __gmpz_set
#define mpz_set_ui __gmpz_set_ui
#define mpz_mul __gmpz_mul
#define mpz_mul_ui __gmpz_mul_ui
#define mpz_add __gmpz_add
#define mpz_add_ui __gmpz_add_ui
#define mpz_mul_2exp __gmpz_mul_2exp
#define mpz_fdiv_q_2exp __gmpz_fdiv_q_2exp
#define mpz_fdiv_r_2exp __gmpz_fdiv_r_2exp
#define mpz_ui_pow_ui __gmpz_ui_pow_ui
#define mpz_sizeinbase __gmpz_sizeinbase
#define mpz_getlimbn __gmpz_getlimbn
#define mpz_cmp __gmpz_cmp
#define mpz_set_str __gmpz_set_str
#define mpz_get_str __gmpz_get_str
#define mpz_tstbit __gmpz_tstbit
void mpz_init(mpz_ptr);
void mpz_clear(mpz_ptr);
void mpz_set(mpz_ptr, mpz_srcptr);
void mpz_set_ui(mpz_ptr, unsigned long);
void mpz_mul(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_mul_ui(mpz_ptr, mpz_srcptr, unsigned long);
void mpz_add(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_add_ui(mpz_ptr, mpz_srcptr, unsigned long);
void mpz_mul_2exp(mpz_ptr, mpz_srcptr, mp_bitcnt_t);
void mpz_fdiv_q_2exp(mpz_ptr, mpz_srcptr, mp_bitcnt_t);
void mpz_fdiv_r_2exp(mpz_ptr, mpz_srcptr, mp_bitcnt_t);
void mpz_ui_pow_ui(mpz_ptr, unsigned long, unsigned long);
size_t mpz_sizeinbase(mpz_srcptr, int);
mp_limb_t mpz_getlimbn(mpz_srcptr, mp_size_t);
int mpz_cmp(mpz_srcptr, mpz_srcptr);
int mpz_set_str(mpz_ptr, const char *, int);
char *mpz_get_str(char *, int, mpz_srcptr);
int mpz_tstbit(mpz_srcptr, mp_bitcnt_t);
#endif
