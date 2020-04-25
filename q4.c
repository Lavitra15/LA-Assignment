#include <math.h>
#include <float.h > /*for DBL_EPSILON */
#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <time.h>
#include <omp.h>
#define REAL double
#define TRUE 1
#define FALSE 0
#define ZERO 0.
#define ONE 1.
#define TWO 2.
#define VEKTOR 0
#define MACH_EPS DBL_EPSILON
#define ABS(x)(((x) >= 0.) ? (x) : -(x))
#define SQRT(x) sqrt(x)
#define SQR(x)((x) *(x))
#define SWAP(typ, a, b)
{
  typ t;
  t = (a);
  (a) = (b);
  (b) = t;
}
#define BASIS basis()
typedef struct
{
  int n, max;
  REAL * mem;
}

vmblock_t;
static void *vminit(void)
{
  return (vmblock_t*) calloc(1, sizeof(vmblock_t));
}

static int vmcomplete(void *vmblock)
{
  return 1;
}

static void vmfree(void *vmblock)
{
  vmblock_t *vmb = (vmblock_t*) vmblock;
  free(vmb->mem);
  free(vmblock);
}

static void *vmalloc(void *vmblock, int typ, size_t zeilen, size_t spalten)
{
  vmblock_t *vmb = (vmblock_t*) vmblock;
  double *ret = 0;
  if (typ == 0)
  {
    if (vmb->n + zeilen > vmb->max)
    {
      vmb->max = vmb->n + zeilen;
      vmb->mem = (REAL*) realloc(vmb->mem, vmb->max* sizeof(REAL));
    }

    ret = vmb->mem + vmb->n;
    vmb->n += zeilen;
  }

  return ret;
}

static int basis(void) /*find basis used for computer number representation */
{
  REAL x,
  eins,
  b;
  x = eins = b = ONE;
  while ((x + eins) - x == eins)
    x *= TWO;
  while ((x + b) == x)
    b *= TWO;
  return (int)((x + b) - x);
}
#define MAXIT 50
/* Maximal number of iterations per eigenvalue   */
static int balance(int n, REAL *mat[], REAL scal[], int *low, int *high, int basis)
{
  register int i, j;
  int iter, k, m;
  REAL b2, r, c, f, g, s;
  b2 = (REAL)(basis *basis);
  m = 0;
  k = n - 1;
  do {
    iter = FALSE;
    for (j = k; j >= 0; j--)
    {
      for (r = ZERO, i = 0; i <= k; i++)
        if (i != j) r += ABS(mat[j][i]);
      if (r == ZERO)
      {
        scal[k] = (REAL) j;
        if (j != k)
        {
          for (i = 0; i <= k; i++) SWAP(REAL, mat[i][j], mat[i][k])
          for (i = m; i < n; i++) SWAP(REAL, mat[j][i], mat[k][i])
        }

        k--;
        iter = TRUE;
      }
    } /*end of j */
  } /*end of do  */
  while (iter);
  do {
    iter = FALSE;
    for (j = m; j <= k; j++)
    {
      for (c = ZERO, i = m; i <= k; i++)
        if (i != j) c += ABS(mat[i][j]);
      if (c == ZERO)
      {
        scal[m] = (REAL) j;
        if (j != m)
        {
          for (i = 0; i <= k; i++) SWAP(REAL, mat[i][j], mat[i][m])
          for (i = m; i < n; i++) SWAP(REAL, mat[j][i], mat[m][i])
        }

        m++;
        iter = TRUE;
      }
    } /*end of j */
  } /*end of do  */
  while (iter);
  *low = m;
  *high = k;
  for (i = m; i <= k; i++) scal[i] = ONE;
  do {
    iter = FALSE;
    for (i = m; i <= k; i++)
    {
      for (c = r = ZERO, j = m; j <= k; j++)
        if (j != i)
        {
          c += ABS(mat[j][i]);
          r += ABS(mat[i][j]);
        }

      g = r / basis;
      f = ONE;
      s = c + r;
      while (c < g)
      {
        f *= basis;
        c *= b2;
      }

      g = r * basis;
      while (c >= g)
      {
        f /= basis;
        c /= b2;
      }

      if ((c + r) / f < (REAL) 0.95 *s)
      {
        g = ONE / f;
        scal[i] *= f;
        iter = TRUE;
        for (j = m; j < n; j++) mat[i][j] *= g;
        for (j = 0; j <= k; j++) mat[j][i] *= f;
      }
    }
  }

  while (iter);
  return (0);
}

static int balback(int n, int low, int high, REAL scal[], REAL *eivec[])
{
  register int i, j, k;
  REAL s;
  for (i = low; i <= high; i++)
  {
    s = scal[i];
    for (j = 0; j < n; j++) eivec[i][j] *= s;
  }

  for (i = low - 1; i >= 0; i--)
  {
    k = (int) scal[i];
    if (k != i)
      for (j = 0; j < n; j++) SWAP(REAL, eivec[i][j], eivec[k][j])
  }

  for (i = high + 1; i < n; i++)
  {
    k = (int) scal[i];
    if (k != i)
      for (j = 0; j < n; j++) SWAP(REAL, eivec[i][j], eivec[k][j])
  }

  return (0);
}

static int elmhes(int n, int low, int high, REAL *mat[], int perm[])
{
  register int i, j, m;
  REAL x, y;
  for (m = low + 1; m < high; m++)
  {
    i = m;
    x = ZERO;
    for (j = m; j <= high; j++)
      if (ABS(mat[j][m - 1]) > ABS(x))
      {
        x = mat[j][m - 1];
        i = j;
      }

    perm[m] = i;
    if (i != m)
    {
      for (j = m - 1; j < n; j++) SWAP(REAL, mat[i][j], mat[m][j])
      for (j = 0; j <= high; j++) SWAP(REAL, mat[j][i], mat[j][m])
    }

    if (x != ZERO)
    {
      for (i = m + 1; i <= high; i++)
      {
        y = mat[i][m - 1];
        if (y != ZERO)
        {
          y = mat[i][m - 1] = y / x;
          for (j = m; j < n; j++) mat[i][j] -= y *mat[m][j];
          for (j = 0; j <= high; j++) mat[j][m] += y *mat[j][i];
        }
      } /*end i */
    }
  } /*end m */
  return (0);
}

static int elmtrans(int n, int low, int high, REAL *mat[], int perm[], REAL *h[])
{
  register int k, i, j;
  for (i = 0; i < n; i++)
  {
    for (k = 0; k < n; k++) h[i][k] = ZERO;
    h[i][i] = ONE;
  }

  for (i = high - 1; i > low; i--)
  {
    j = perm[i];
    for (k = i + 1; k <= high; k++) h[k][i] = mat[k][i - 1];
    if (i != j)
    {
      for (k = i; k <= high; k++)
      {
        h[i][k] = h[j][k];
        h[j][k] = ZERO;
      }

      h[j][i] = ONE;
    }
  }

  return (0);
}

static int orthes(int n, int low, int high, REAL *mat[], REAL d[])
{
  int i, j, m; /*loop variables                                  */
  REAL s, x = ZERO, y, eps;
  eps = (REAL) 128.0 * MACH_EPS;
  for (m = low + 1; m < high; m++)
  {
    for (y = ZERO, i = high; i >= m; i--)
      x = mat[i][m - 1],
      d[i] = x,
      y = y + x * x;
    if (y <= eps)
      s = ZERO;
    else
    {
      s = (x >= ZERO) ? -SQRT(y) : SQRT(y);
      y -= x * s;
      d[m] = x - s;

      for (j = m; j < n; j++) /*multiply mat from the  */
      { /*left by  (E-(u*uT)/y)  */
        for (x = ZERO, i = high; i >= m; i--)
          x += d[i] *mat[i][j];
        for (x /= y, i = m; i <= high; i++)
          mat[i][j] -= x *d[i];
      }

      for (i = 0; i <= high; i++) /*multiply mat from the  */
      { /*right by  (E-(u*uT)/y) */
        for (x = ZERO, j = high; j >= m; j--)
          x += d[j] *mat[i][j];
        for (x /= y, j = m; j <= high; j++)
          mat[i][j] -= x *d[j];
      }
    }

    mat[m][m - 1] = s;
  }

  return 0;
}

static int orttrans(int n, int low, int high, REAL *mat[], REAL d[], REAL *v[])
{
  int i, j, m; /*loop variables              */
  REAL x, y;
  for (i = 0; i < n; i++) /*form the unit matrix in v   */
  {
    for (j = 0; j < n; j++)
      v[i][j] = ZERO;
    v[i][i] = ONE;
  }

  for (m = high - 1; m > low; m--) /*apply the transformations   */
  { /*that reduced mat to upper   */
    y = mat[m][m - 1]; /*Hessenberg form also to the */
    if (y != ZERO) /*produces the desired        */
    { /*transformation matrix in v. */
      y *= d[m];
      for (i = m + 1; i <= high; i++)
        d[i] = mat[i][m - 1];
      for (j = m; j <= high; j++)
      {
        for (x = ZERO, i = m; i <= high; i++)
          x += d[i] *v[i][j];
        for (x /= y, i = m; i <= high; i++)
          v[i][j] += x *d[i];
      }
    }
  }

  return 0;
}

static int hqrvec(int n, int low, int high, REAL *h[], REAL wr[], REAL wi[], REAL *eivec[])
{
  int i, j, k;
  int l, m, en, na;
  REAL p, q, r = ZERO, s = ZERO, t, w, x, y, z = ZERO,
    ra, sa, vr, vi, norm;
  for (norm = ZERO, i = 0; i < n; i++) /*find norm of h       */
  {
    for (j = i; j < n; j++) norm += ABS(h[i][j]);
  }

  if (norm == ZERO) return (1); /*zero matrix          */ #
  pragma omp parallel shared(h) private(en, i, j)
  {#
    pragma omp
    for schedule(static)
    for (en = n - 1; en >= 0; en--) /*transform back       */
    {
      p = wr[en];
      q = wi[en];
      na = en - 1;
      if (q == ZERO)
      {
        m = en;
        h[en][en] = ONE;
        for (i = na; i >= 0; i--)
        {
          w = h[i][i] - p;
          r = h[i][en];
          for (j = m; j <= na; j++) r += h[i][j] *h[j][en];
          if (wi[i] < ZERO)
          {
            z = w;
            s = r;
          }
          else
          {
            m = i;
            if (wi[i] == ZERO)
              h[i][en] = -r / ((w != ZERO) ? (w) : (MACH_EPS *norm));
            else
            {
              x = h[i][i + 1];
              y = h[i + 1][i];
              q = SQR(wr[i] - p) + SQR(wi[i]);
              h[i][en] = t = (x *s - z *r) / q;
              h[i + 1][en] = ((ABS(x) > ABS(z)) ? (-r - w *t) / x : (-s - y *t) / z);
            }
          } /*wi[i] >= 0  */
        } /* end i     */
      } /*end q = 0  */
      else if (q < ZERO)
      {
        m = na;
        if (ABS(h[en][na]) > ABS(h[na][en]))
        {
          h[na][na] = -(h[en][en] - p) / h[en][na];
          h[na][en] = -q / h[en][na];
        }
        else
        {
          REAL complex c;
          c = -h[na][en] / (h[na][na] - p + q *I);
          h[na][na] = creal(c);
          h[na][en] = cimag(c);
        }

        h[en][na] = ONE;
        h[en][en] = ZERO;
        for (i = na - 1; i >= 0; i--)
        {
          w = h[i][i] - p;
          ra = h[i][en];
          sa = ZERO;
          for (j = m; j <= na; j++)
          {
            ra += h[i][j] *h[j][na];
            sa += h[i][j] *h[j][en];
          }

          if (wi[i] < ZERO)
          {
            z = w;
            r = ra;
            s = sa;
          }
          else
          {
            m = i;
            if (wi[i] == ZERO)
            {
              /*comdiv (-ra, -sa, w, q, &h[i][na], &h[i][en]); */
              REAL complex c;
              c = (-ra - sa *I) / (w + q *I);
              h[i][na] = creal(c);
              h[i][en] = cimag(c);
            }
            else
            {
              x = h[i][i + 1];
              y = h[i + 1][i];
              vr = SQR(wr[i] - p) + SQR(wi[i]) - SQR(q);
              vi = TWO *q *(wr[i] - p);
              if (vr == ZERO && vi == ZERO)
                vr = MACH_EPS *norm *(ABS(w) + ABS(q) + ABS(x) + ABS(y) + ABS(z));
              {
                REAL complex c = (x *r - z *ra + q *sa + I *(x *s - z *sa - q *ra)) / (vr + I *vi);
                h[i][na] = creal(c);
                h[i][en] = cimag(c);
              }

              if (ABS(x) > ABS(z) + ABS(q))
              {
                h[i + 1][na] = (-ra - w *h[i][na] + q *h[i][en]) / x;
                h[i + 1][en] = (-sa - w *h[i][en] - q *h[i][na]) / x;
              }
              else
              {
                REAL complex c;
                c = (-r - y *h[i][na] + I *(-s - y *h[i][en])) / (z + I *q);
                h[i + 1][na] = creal(c);
                h[i + 1][en] = cimag(c);
              }
            } /*end wi[i] > 0  */
          } /*end wi[i] >= 0  */
        } /*end i            */
      } /* if q < 0        */
    } /*end  en           */
  }

  for (i = 0; i < n; i++) /*Eigenvectors for the evalues for */
    if (i < low || i > high) /*rows < low  and rows > high     */
      for (k = i + 1; k < n; k++) eivec[i][k] = h[i][k];
  for (j = n - 1; j >= low; j--)
  {
    m = (j <= high) ? j : high;
    if (wi[j] < ZERO)
    {
      for (l = j - 1, i = low; i <= high; i++)
      {
        for (y = z = ZERO, k = low; k <= m; k++)
        {
          y += eivec[i][k] *h[k][l];
          z += eivec[i][k] *h[k][j];
        }

        eivec[i][l] = y;
        eivec[i][j] = z;
      }
    }
    else
    if (wi[j] == ZERO)
    {
      for (i = low; i <= high; i++)
      {
        for (z = ZERO, k = low; k <= m; k++)
          z += eivec[i][k] *h[k][j];
        eivec[i][j] = z;
      }
    }
  } /* end j  */
  return (0);
}

static int hqr2(int vec, int n, int low, int high, REAL *h[], REAL wr[], REAL wi[], REAL *eivec[], int cnt[])
{
  int i, j;
  int na, en, iter, k, l, m;
  REAL p = ZERO, q = ZERO, r = ZERO, s, t, w, x, y, z;
  for (i = 0; i < n; i++)
    if (i < low || i > high)
    {
      wr[i] = h[i][i];
      wi[i] = ZERO;
      cnt[i] = 0;
    }

  en = high;
  t = ZERO;
  while (en >= low)
  {
    iter = 0;
    na = en - 1;
    for (;;)
    {
      for (l = en; l > low; l--) /*search for small      */
        if (ABS(h[l][l - 1]) <= /*subdiagonal element   */
          MACH_EPS *(ABS(h[l - 1][l - 1]) + ABS(h[l][l]))) break;
      x = h[en][en];
      if (l == en) /*found one evalue     */
      {
        wr[en] = h[en][en] = x + t;
        wi[en] = ZERO;
        cnt[en] = iter;
        en--;
        break;
      }

      y = h[na][na];
      w = h[en][na] *h[na][en];
      if (l == na) /*found two evalues    */
      {
        p = (y - x) *0.5;
        q = p *p + w;
        z = SQRT(ABS(q));
        x = h[en][en] = x + t;
        h[na][na] = y + t;
        cnt[en] = -iter;
        cnt[na] = iter;
        if (q >= ZERO)
        { /*real eigenvalues     */
          z = (p < ZERO) ? (p - z) : (p + z);
          wr[na] = x + z;
          wr[en] = s = x - w / z;
          wi[na] = wi[en] = ZERO;
          x = h[en][na];
          r = SQRT(x *x + z *z);
          if (vec)
          {
            p = x / r;
            q = z / r;
            for (j = na; j < n; j++)
            {
              z = h[na][j];
              h[na][j] = q *z + p *h[en][j];
              h[en][j] = q *h[en][j] - p * z;
            }

            for (i = 0; i <= en; i++)
            {
              z = h[i][na];
              h[i][na] = q *z + p *h[i][en];
              h[i][en] = q *h[i][en] - p * z;
            }

            for (i = low; i <= high; i++)
            {
              z = eivec[i][na];
              eivec[i][na] = q *z + p *eivec[i][en];
              eivec[i][en] = q *eivec[i][en] - p * z;
            }
          } /*end if (vec) */
        } /*end if (q >= ZERO) */
        else /*pair of complex      */
        { /*conjugate evalues    */
          wr[na] = wr[en] = x + p;
          wi[na] = z;
          wi[en] = -z;
        }

        en -= 2;
        break;
      } /*end if (l == na) */
      if (iter >= MAXIT)
      {
        cnt[en] = MAXIT + 1;
        return (en); /*MAXIT Iterations     */
      }

      if ((iter != 0) && (iter % 10 == 0))
      {
        t += x;
        for (i = low; i <= en; i++) h[i][i] -= x;
        s = ABS(h[en][na]) + ABS(h[na][en - 2]);
        x = y = (REAL) 0.75 * s;
        w = -(REAL) 0.4375 *s * s;
      }

      iter++;
      for (m = en - 2; m >= l; m--)
      {
        z = h[m][m];
        r = x - z;
        s = y - z;
        p = (r *s - w) / h[m + 1][m] + h[m][m + 1];
        q = h[m + 1][m + 1] - z - r - s;
        r = h[m + 2][m + 1];
        s = ABS(p) + ABS(q) + ABS(r);
        p /= s;
        q /= s;
        r /= s;
        if (m == l) break;
        if (ABS(h[m][m - 1]) *(ABS(q) + ABS(r))<=
          MACH_EPS* ABS(p) *
          (ABS(h[m - 1][m - 1]) + ABS(z) + ABS(h[m + 1][m + 1])))
          break;
      }

      for (i = m + 2; i <= en; i++) h[i][i - 2] = ZERO;
      for (i = m + 3; i <= en; i++) h[i][i - 3] = ZERO;
      for (k = m; k <= na; k++)
      {
        if (k != m) /*double  QR step, for rows l to en  */
        { /*and columns m to en                */
          p = h[k][k - 1];
          q = h[k + 1][k - 1];
          r = (k != na) ? h[k + 2][k - 1] : ZERO;
          x = ABS(p) + ABS(q) + ABS(r);
          if (x == ZERO) continue; /* next k        */
          p /= x;
          q /= x;
          r /= x;
        }

        s = SQRT(p *p + q *q + r *r);
        if (p < ZERO) s = -s;
        if (k != m) h[k][k - 1] = -s * x;
        else if (l != m)
          h[k][k - 1] = -h[k][k - 1];
        p += s;
        x = p / s;
        y = q / s;
        z = r / s;
        q /= p;
        r /= p;
        for (j = k; j < n; j++) /*modify rows          */
        {
          p = h[k][j] + q *h[k + 1][j];
          if (k != na)
          {
            p += r *h[k + 2][j];
            h[k + 2][j] -= p * z;
          }

          h[k + 1][j] -= p * y;
          h[k][j] -= p * x;
        }

        j = (k + 3 < en) ? (k + 3) : en;
        for (i = 0; i <= j; i++) /*modify columns       */
        {
          p = x *h[i][k] + y *h[i][k + 1];
          if (k != na)
          {
            p += z *h[i][k + 2];
            h[i][k + 2] -= p * r;
          }

          h[i][k + 1] -= p * q;
          h[i][k] -= p;
        }

        if (vec) /*if eigenvectors are needed ..................*/
        {
          for (i = low; i <= high; i++)
          {
            p = x *eivec[i][k] + y *eivec[i][k + 1];
            if (k != na)
            {
              p += z *eivec[i][k + 2];
              eivec[i][k + 2] -= p * r;
            }

            eivec[i][k + 1] -= p * q;
            eivec[i][k] -= p;
          }
        }
      } /*end k          */
    } /*end for (; ;) */
  } /*while (en >= low)                      All evalues found    */
  if (vec) /*transform evectors back  */
    if (hqrvec(n, low, high, h, wr, wi, eivec)) return (99);
  return (0);
}

static int norm_1(int n, REAL *v[], REAL wi[])
{
  int i, j;
  REAL maxi, tr, ti;
  if (n < 1) return (1);#
  pragma omp parallel shared(v) private(i, j)
  {#
    pragma omp
    for schedule(static)
    for (j = 0; j < n; j++)
    {
      if (wi[j] == ZERO)
      {
        maxi = v[0][j];
        for (i = 1; i < n; i++)
          if (ABS(v[i][j]) > ABS(maxi)) maxi = v[i][j];
        if (maxi != ZERO)
        {
          maxi = ONE / maxi;
          for (i = 0; i < n; i++) v[i][j] *= maxi;
        }
      }
      else
      {
        tr = v[0][j];
        ti = v[0][j + 1];
        for (i = 1; i < n; i++)
          if (cabs(v[i][j] + I *v[i][j + 1]) > cabs(tr + I *ti))
          {
            tr = v[i][j];
            ti = v[i][j + 1];
          }

        if (tr != ZERO || ti != ZERO)
          for (i = 0; i < n; i++)
          {
            REAL complex c;
            c = (v[i][j] + I *v[i][j + 1]) / (tr + I *ti);
            v[i][j] = creal(c);
            v[i][j + 1] = cimag(c);
          }

        j++; /*raise j by two */
      }
    }
  }

  return (0);
}

static int eigen(int vec, int ortho, int ev_norm, int n, REAL *mat[], REAL *eivec[], REAL valre[], REAL valim[], int cnt[])
{
  int i;
  int low, high, rc;
  REAL *scale,
    *d = NULL;
  void *vmblock;
  if (n < 1) return (1); /* n >= 1 ............*/
  if (valre == NULL || valim == NULL || mat == NULL || cnt == NULL)
    return (1);
  for (i = 0; i < n; i++)
    if (mat[i] == NULL) return (1);
  for (i = 0; i < n; i++) cnt[i] = 0;
  if (n == 1) /* n = 1 .............*/
  {
    eivec[0][0] = ONE;
    valre[0] = mat[0][0];
    valim[0] = ZERO;
    return (0);
  }

  if (vec)
  {
    if (eivec == NULL) return (1);
    for (i = 0; i < n; i++)
      if (eivec[i] == NULL) return (1);
  }

  vmblock = vminit();
  scale = (REAL*) vmalloc(vmblock, VEKTOR, n, 0);
  if (!vmcomplete(vmblock)) /*memory error         */
    return 2;
  if (vec && ortho) /*with Eigenvectors     */
  {
    d = (REAL*) vmalloc(vmblock, VEKTOR, n, 0);
    if (!vmcomplete(vmblock))
    {
      vmfree(vmblock);
      return 1;
    }
  } /*balance mat for nearly */
  rc = balance(n, mat, scale, &low, &high, BASIS); /*one norms              */
  if (rc)
  {
    vmfree(vmblock);
    return (100 + rc);
  }

  if (ortho) rc = orthes(n, low, high, mat, d);
  else rc = elmhes(n, low, high, mat, cnt); /* reduce mat to upper   */
  if (rc) /* Hessenberg form       */
  {
    vmfree(vmblock);
    return (200 + rc);
  }

  if (vec) /* initialize eivec      */
  {
    if (ortho) rc = orttrans(n, low, high, mat, d, eivec);
    else rc = elmtrans(n, low, high, mat, cnt, eivec);
    if (rc)
    {
      vmfree(vmblock);
      return (300 + rc);
    }
  }

  rc = hqr2(vec, n, low, high, mat, valre, valim, eivec, cnt); /* algorithm to obtain   */
  if (rc) /* eigenvalues           */
  {
    vmfree(vmblock);
    return (400 + rc);
  }

  if (vec)
  {
    rc = balback(n, low, high, scale, eivec); /* eigenvaectors are to  */
    if (rc) /* be determined         */
    {
      vmfree(vmblock);
      return (500 + rc);
    }

    if (ev_norm)
      rc = norm_1(n, eivec, valim); /*normalize eigenvectors */
    if (rc)
    {
      vmfree(vmblock);
      return (600 + rc);
    }
  }

  vmfree(vmblock); /*free buffers           */
  return (0);
}

int n_eigeng(double *_a, int n, double *evalr, double *evali, double *_evec, double *b)
{
  double **a, **evec = 0;
  int i, j, *cnt;
  a = (double **) calloc(n, sizeof(void*));
  if (_evec) evec = (double **) calloc(n, sizeof(void*));
  cnt = (int*) calloc(n, sizeof(int));#
  pragma omp parallel shared(evec) private(i)
  {#
    pragma omp
    for schedule(static)
    for (i = 0; i < n; ++i)
    {
      a[i] = _a + i * n;
      if (_evec) evec[i] = _evec + i * n;
    }
  }

  eigen(_evec ? 1 : 0, 0, 1, n, a, evec, evalr, evali, cnt);
  if (_evec)
  {
    double tmp;
    for (j = 0; j < n; ++j)
    {
      tmp = 0.0;#
      pragma omp parallel shared(evec) private(i)
      {#
        pragma omp
        for schedule(static)
        for (i = 0; i < n; ++i) tmp += SQR(evec[i][j]);
      }

      tmp = SQRT(tmp);#
      pragma omp parallel shared(evec) private(i)
      {#
        pragma omp
        for schedule(static)
        for (i = 0; i < n; ++i) evec[i][j] /= tmp;
      }
    }
  }

  free(a);
  free(evec);
  free(cnt);
  return 0;
}

static int hqrvec1(int n int low, int high, REAL *h[], REAL wr[], REAL wi[], REAL *eivec[])
{
  int i, j, k;
  int l, m, en, na;
  REAL p, q, r = ZERO, s = ZERO, t, w, x, y, z = ZERO, ra, sa, vr, vi, norm;
  for (norm = ZERO, i = 0; i < n; i++) /*find norm of h       */
    for (j = i; j < n; j++) norm += ABS(h[i][j]);
  if (norm == ZERO) return (1); /*zero matrix          */
  for (en = n - 1; en >= 0; en--) /*transform back       */
  {
    p = wr[en];
    q = wi[en];
    na = en - 1;
    if (q == ZERO)
    {
      m = en;
      h[en][en] = ONE;
      for (i = na; i >= 0; i--)
      {
        w = h[i][i] - p;
        r = h[i][en];
        for (j = m; j <= na; j++) r += h[i][j] *h[j][en];
        if (wi[i] < ZERO)
        {
          z = w;
          s = r;
        }
        else
        {
          m = i;
          if (wi[i] == ZERO)
            h[i][en] = -r / ((w != ZERO) ? (w) : (MACH_EPS *norm));
          else
          {
            x = h[i][i + 1];
            y = h[i + 1][i];
            q = SQR(wr[i] - p) + SQR(wi[i]);
            h[i][en] = t = (x *s - z *r) / q;
            h[i + 1][en] = ((ABS(x) > ABS(z)) ? (-r - w *t) / x : (-s - y *t) / z);
          }
        } /*wi[i] >= 0  */
      } /* end i     */
    } /*end q = 0  */
    else if (q < ZERO)
    {
      m = na;
      if (ABS(h[en][na]) > ABS(h[na][en]))
      {
        h[na][na] = -(h[en][en] - p) / h[en][na];
        h[na][en] = -q / h[en][na];
      }
      else
      {
        REAL complex c;
        c = -h[na][en] / (h[na][na] - p + q *I);
        h[na][na] = creal(c);
        h[na][en] = cimag(c);
      }

      h[en][na] = ONE;
      h[en][en] = ZERO;
      for (i = na - 1; i >= 0; i--)
      {
        w = h[i][i] - p;
        ra = h[i][en];
        sa = ZERO;
        for (j = m; j <= na; j++)
        {
          ra += h[i][j] *h[j][na];
          sa += h[i][j] *h[j][en];
        }

        if (wi[i] < ZERO)
        {
          z = w;
          r = ra;
          s = sa;
        }
        else
        {
          m = i;
          if (wi[i] == ZERO)
          {
            REAL complex c;
            c = (-ra - sa *I) / (w + q *I);
            h[i][na] = creal(c);
            h[i][en] = cimag(c);
          }
          else
          {
            x = h[i][i + 1];
            y = h[i + 1][i];
            vr = SQR(wr[i] - p) + SQR(wi[i]) - SQR(q);
            vi = TWO *q *(wr[i] - p);
            if (vr == ZERO && vi == ZERO)
              vr = MACH_EPS *norm *
              (ABS(w) + ABS(q) + ABS(x) + ABS(y) + ABS(z));
            {
              REAL complex c;
              c = (x *r - z *ra + q *sa + I *(x *s - z *sa - q *ra)) / (vr + I *vi);
              h[i][na] = creal(c);
              h[i][en] = cimag(c);
            }

            if (ABS(x) > ABS(z) + ABS(q))
            {
              h[i + 1][na] = (-ra - w *h[i][na] + q *h[i][en]) / x;
              h[i + 1][en] = (-sa - w *h[i][en] - q *h[i][na]) / x;
            }
            else
            {
              REAL complex c;
              c = (-r - y *h[i][na] + I *(-s - y *h[i][en])) / (z + I *q);
              h[i + 1][na] = creal(c);
              h[i + 1][en] = cimag(c);
            }
          } /*end wi[i] > 0  */
        } /*end wi[i] >= 0  */
      } /*end i            */
    } /* if q < 0        */
  } /*end  en           */
  for (i = 0; i < n; i++) /*Eigenvectors for the evalues for */
    if (i < low || i > high) /*rows < low  and rows > high     */
      for (k = i + 1; k < n; k++) eivec[i][k] = h[i][k];
  for (j = n - 1; j >= low; j--)
  {
    m = (j <= high) ? j : high;
    if (wi[j] < ZERO)
    {
      for (l = j - 1, i = low; i <= high; i++)
      {
        for (y = z = ZERO, k = low; k <= m; k++)
        {
          y += eivec[i][k] *h[k][l];
          z += eivec[i][k] *h[k][j];
        }

        eivec[i][l] = y;
        eivec[i][j] = z;
      }
    }
    else
    if (wi[j] == ZERO)
    {
      for (i = low; i <= high; i++)
      {
        for (z = ZERO, k = low; k <= m; k++)
          z += eivec[i][k] *h[k][j];
        eivec[i][j] = z;
      }
    }
  } /* end j  */
  return (0);
}

static int hqr21(int vec, int n, int low, int high, REAL *h[], REAL wr[], REAL wi[], REAL *eivec[], int cnt[])
{
  int i, j;
  int na, en, iter, k, l, m;
  REAL p = ZERO, q = ZERO, r = ZERO, s, t, w, x, y, z;
  for (i = 0; i < n; i++)
    if (i < low || i > high)
    {
      wr[i] = h[i][i];
      wi[i] = ZERO;
      cnt[i] = 0;
    }

  en = high;
  t = ZERO;
  while (en >= low)
  {
    iter = 0;
    na = en - 1;
    for (;;)
    {
      for (l = en; l > low; l--) /*search for small      */
        if (ABS(h[l][l - 1]) <= /*subdiagonal element   */
          MACH_EPS *(ABS(h[l - 1][l - 1]) + ABS(h[l][l]))) break;
      x = h[en][en];
      if (l == en) /*found one evalue     */
      {
        wr[en] = h[en][en] = x + t;
        wi[en] = ZERO;
        cnt[en] = iter;
        en--;
        break;
      }

      y = h[na][na];
      w = h[en][na] *h[na][en];
      if (l == na) /*found two evalues    */
      {
        p = (y - x) *0.5;
        q = p *p + w;
        z = SQRT(ABS(q));
        x = h[en][en] = x + t;
        h[na][na] = y + t;
        cnt[en] = -iter;
        cnt[na] = iter;
        if (q >= ZERO)
        { /*real eigenvalues     */
          z = (p < ZERO) ? (p - z) : (p + z);
          wr[na] = x + z;
          wr[en] = s = x - w / z;
          wi[na] = wi[en] = ZERO;
          x = h[en][na];
          r = SQRT(x *x + z *z);
          if (vec)
          {
            p = x / r;
            q = z / r;
            for (j = na; j < n; j++)
            {
              z = h[na][j];
              h[na][j] = q *z + p *h[en][j];
              h[en][j] = q *h[en][j] - p * z;
            }

            for (i = 0; i <= en; i++)
            {
              z = h[i][na];
              h[i][na] = q *z + p *h[i][en];
              h[i][en] = q *h[i][en] - p * z;
            }

            for (i = low; i <= high; i++)
            {
              z = eivec[i][na];
              eivec[i][na] = q *z + p *eivec[i][en];
              eivec[i][en] = q *eivec[i][en] - p * z;
            }
          } /*end if (vec) */
        } /*end if (q >= ZERO) */
        else /*pair of complex      */
        { /*conjugate evalues    */
          wr[na] = wr[en] = x + p;
          wi[na] = z;
          wi[en] = -z;
        }

        en -= 2;
        break;
      } /*end if (l == na) */
      if (iter >= MAXIT)
      {
        cnt[en] = MAXIT + 1;
        return (en); /*MAXIT Iterations     */
      }

      if ((iter != 0) && (iter % 10 == 0))
      {
        t += x;
        for (i = low; i <= en; i++) h[i][i] -= x;
        s = ABS(h[en][na]) + ABS(h[na][en - 2]);
        x = y = (REAL) 0.75 * s;
        w = -(REAL) 0.4375 *s * s;
      }

      iter++;
      for (m = en - 2; m >= l; m--)
      {
        z = h[m][m];
        r = x - z;
        s = y - z;
        p = (r *s - w) / h[m + 1][m] + h[m][m + 1];
        q = h[m + 1][m + 1] - z - r - s;
        r = h[m + 2][m + 1];
        s = ABS(p) + ABS(q) + ABS(r);
        p /= s;
        q /= s;
        r /= s;
        if (m == l) break;
        if (ABS(h[m][m - 1]) *(ABS(q) + ABS(r))<=
          MACH_EPS* ABS(p) *
          (ABS(h[m - 1][m - 1]) + ABS(z) + ABS(h[m + 1][m + 1])))
          break;
      }

      for (i = m + 2; i <= en; i++) h[i][i - 2] = ZERO;
      for (i = m + 3; i <= en; i++) h[i][i - 3] = ZERO;
      for (k = m; k <= na; k++)
      {
        if (k != m) /*double  QR step, for rows l to en  */
        { /*and columns m to en                */
          p = h[k][k - 1];
          q = h[k + 1][k - 1];
          r = (k != na) ? h[k + 2][k - 1] : ZERO;
          x = ABS(p) + ABS(q) + ABS(r);
          if (x == ZERO) continue; /* next k        */
          p /= x;
          q /= x;
          r /= x;
        }

        s = SQRT(p *p + q *q + r *r);
        if (p < ZERO) s = -s;
        if (k != m) h[k][k - 1] = -s * x;
        else if (l != m)
          h[k][k - 1] = -h[k][k - 1];
        p += s;
        x = p / s;
        y = q / s;
        z = r / s;
        q /= p;
        r /= p;
        for (j = k; j < n; j++) /*modify rows          */
        {
          p = h[k][j] + q *h[k + 1][j];
          if (k != na)
          {
            p += r *h[k + 2][j];
            h[k + 2][j] -= p * z;
          }

          h[k + 1][j] -= p * y;
          h[k][j] -= p * x;
        }

        j = (k + 3 < en) ? (k + 3) : en;
        for (i = 0; i <= j; i++) /*modify columns       */
        {
          p = x *h[i][k] + y *h[i][k + 1];
          if (k != na)
          {
            p += z *h[i][k + 2];
            h[i][k + 2] -= p * r;
          }

          h[i][k + 1] -= p * q;
          h[i][k] -= p;
        }

        if (vec) /*if eigenvectors are needed ..................*/
        {
          for (i = low; i <= high; i++)
          {
            p = x *eivec[i][k] + y *eivec[i][k + 1];
            if (k != na)
            {
              p += z *eivec[i][k + 2];
              eivec[i][k + 2] -= p * r;
            }

            eivec[i][k + 1] -= p * q;
            eivec[i][k] -= p;
          }
        }
      } /*end k          */
    } /*end for (; ;) */
  } /*while (en >= low)                      All evalues found    */
  if (vec) /*transform evectors back  */
    if (hqrvec1(n, low, high, h, wr, wi, eivec)) return (99);
  return (0);
}

static int norm_11(int n, REAL *v[], REAL wi[])
{
  int i, j;
  REAL maxi, tr, ti;
  if (n < 1) return (1);
  for (j = 0; j < n; j++)
  {
    if (wi[j] == ZERO)
    {
      maxi = v[0][j];
      for (i = 1; i < n; i++)
        if (ABS(v[i][j]) > ABS(maxi)) maxi = v[i][j];
      if (maxi != ZERO)
      {
        maxi = ONE / maxi;
        for (i = 0; i < n; i++) v[i][j] *= maxi;
      }
    }
    else
    {
      tr = v[0][j];
      ti = v[0][j + 1];
      for (i = 1; i < n; i++)
        if (cabs(v[i][j] + I *v[i][j + 1]) > cabs(tr + I *ti))
        {
          tr = v[i][j];
          ti = v[i][j + 1];
        }

      if (tr != ZERO || ti != ZERO)
        for (i = 0; i < n; i++)
        {
          REAL complex c;
          c = (v[i][j] + I *v[i][j + 1]) / (tr + I *ti);
          v[i][j] = creal(c);
          v[i][j + 1] = cimag(c);
        }

      j++; /*raise j by two */
    }
  }

  return (0);
}

static int eigen11(int vec, int ortho, int ev_norm, int n, REAL *mat[], REAL *eivec[], REAL valre[], REAL valim[], int cnt[])
{
  int i;
  int low, high, rc;
  REAL *scale, *d = NULL;
  void *vmblock;
  if (n < 1) return (1); /* n >= 1 ............*/
  if (valre == NULL || valim == NULL || mat == NULL || cnt == NULL)
    return (1);
  for (i = 0; i < n; i++)
    if (mat[i] == NULL) return (1);
  for (i = 0; i < n; i++) cnt[i] = 0;
  if (n == 1) /* n = 1 .............*/
  {
    eivec[0][0] = ONE;
    valre[0] = mat[0][0];
    valim[0] = ZERO;
    return (0);
  }

  if (vec)
  {
    if (eivec == NULL) return (1);
    for (i = 0; i < n; i++)
      if (eivec[i] == NULL) return (1);
  }

  vmblock = vminit();
  scale = (REAL*) vmalloc(vmblock, VEKTOR, n, 0);
  if (!vmcomplete(vmblock)) /*memory error         */
    return 2;
  if (vec && ortho) /*with Eigenvectors     */
  { /*Hessenberg reduction? */
    d = (REAL*) vmalloc(vmblock, VEKTOR, n, 0);
    if (!vmcomplete(vmblock))
    {
      vmfree(vmblock);
      return 1;
    }
  } /*balance mat for nearly */
  rc = balance(n, mat, scale, &low, &high, BASIS); /*one norms              */
  if (rc)
  {
    vmfree(vmblock);
    return (100 + rc);
  }

  if (ortho) rc = orthes(n, low, high, mat, d);
  else rc = elmhes(n, low, high, mat, cnt); /* reduce mat to upper   */
  if (rc) /* Hessenberg form       */
  {
    vmfree(vmblock);
    return (200 + rc);
  }

  if (vec) /* initialize eivec      */
  {
    if (ortho)
      rc = orttrans(n, low, high, mat, d, eivec);
    else
      rc = elmtrans(n, low, high, mat, cnt, eivec);
    if (rc)
    {
      vmfree(vmblock);
      return (300 + rc);
    }
  }

  rc = hqr21(vec, n, low, high, mat, valre, valim, eivec, cnt); /* algorithm to obtain   */
  if (rc) /* eigenvalues           */
  {
    vmfree(vmblock);
    return (400 + rc);
  }

  if (vec)
  {
    rc = balback(n, low, high, /* reverse balancing if  */
      scale, eivec); /* eigenvaectors are to  */
    if (rc) /* be determined         */
    {
      vmfree(vmblock);
      return (500 + rc);
    }

    if (ev_norm)
      rc = norm_11(n, eivec, valim); /*normalize eigenvectors */
    if (rc)
    {
      vmfree(vmblock);
      return (600 + rc);
    }
  }

  vmfree(vmblock); /*free buffers           */
  return (0);
}

int n_eigeng1(double *_a, int n, double *evalr, double *evali, double *_evec, double *b)
{
  double **a, **evec = 0;
  int i, j, *cnt;
  a = (double **) calloc(n, sizeof(void*));
  if (_evec) evec = (double **) calloc(n, sizeof(void*));
  cnt = (int*) calloc(n, sizeof(int));
  {
    for (i = 0; i < n; ++i)
    {
      a[i] = _a + i * n;
      if (_evec) evec[i] = _evec + i * n;
    }
  }

  eigen11(_evec ? 1 : 0, 0, 1, n, a, evec, evalr, evali, cnt);
  if (_evec)
  {
    double tmp;
    for (j = 0; j < n; ++j)
    {
      tmp = 0.0;
      {
        for (i = 0; i < n; ++i) tmp += SQR(evec[i][j]);
      }

      tmp = SQRT(tmp);
      {
        for (i = 0; i < n; ++i) evec[i][j] /= tmp;
      }
    }
  }

  free(a);
  free(evec);
  free(cnt);
  return 0;
}

int main(void)
{
  int n;
  printf("Enter the order of the matrix:");
  scanf("%d", &n);
  double *b = malloc(n *n* sizeof(double));
  double *b1 = malloc(n *n* sizeof(double));
  for (int i = 0; i < n; i++)
  {
    for (int j = 0; j < n; j++)
    {*(b + i *n + j) = rand(); *(b1 + i *n + j) = *(b + i *n + j);
    }
  }

  double *mem, *evalr, *evali, *evec;
  int i, j;
  mem = (double*) calloc(n *n + 2 *n, sizeof(double));
  evec = mem;
  evalr = evec + n * n;
  evali = evalr + n;
  printf("\n\n");
  clock_t start, end;
  start = clock();
  n_eigeng(b + 0, n, evalr, evali, evec, b);
  end = clock();
  printf("Time taken with parallelization:%f\n", ((float)(end - start)) / CLOCKS_PER_SEC);
  double *mem1, *evalr1, *evali1, *evec1;
  mem1 = (double*) calloc(n *n + 2 *n, sizeof(double));
  evec1 = mem;
  evalr1 = evec + n * n;
  evali1 = evalr + n;
  start = clock();
  n_eigeng1(b1 + 0, n, evalr1, evali1, evec1, b1);
  end = clock();
  printf("Time taken without parallelization:%f\n", ((float)(end - start)) / CLOCKS_PER_SEC);
  free(mem);
  return 0;
}