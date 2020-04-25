#include<stdio.h>
#include<math.h>
#include<omp.h>
#define MAXN 25
float determinant(float [][MAXN], float);
void cofactor(float [][MAXN], float,float [][MAXN],float [][MAXN],float);
void transpose(float [][MAXN], float [][MAXN], float,float [][MAXN],float [][MAXN],float);
int findmultiply(float a[][MAXN],float b[][MAXN],float c[][MAXN],int m,int n,int p)
{
int i,j,k;
#pragma omp parallel shared(a,b,c) private(i,j,k)
{
#pragma omp for schedule(static)
for (i=0; i<m; ++i){
for (j=0; j<n; ++j){
a[i][j]=0.;
for (k=0; k<p; ++k){
a[i][j]=(a[i][j])+((b[i][k])*(c[k][j]));
}
}
}
}
return 0;
}
int main()
{
float a[MAXN][MAXN],b[MAXN][MAXN],c[MAXN][MAXN],e[MAXN][MAXN],m,n,d;
int i, j;
printf("Enter the number of the rows of the Matrix (that is m) : ");
scanf("%f", &m);
printf("Enter the number of the columns of the Matrix (that is n) : ");
scanf("%f", &n);
printf("Enter the elements of A %.0fX%.0f Matrix : \n", m, n);
for (i = 0;i < m; i++)
{
for (j = 0;j < n; j++)
{
scanf("%f", &a[i][j]);
c[j][i]=a[i][j];//this is the transpose;
}
}
printf("Enter the elements of B %.0fX%.0f Matrix that is 'm' elements : \n", m,1.0);
for (i = 0;i < m; i++)
{
scanf("%f",&b[i][0]);
}
//m=n;n=n;p=m
findmultiply(e,c,a,n,n,m);
d = determinant(e, n);
if (d == 0)
printf("\nInverse of Entered Matrix is not possible\n");
else
cofactor(e,n,c,b,m);
}
/*For calculating Determinant of the Matrix */
float determinant(float a[MAXN][MAXN], float k)
{
float s = 1, det = 0, b[MAXN][MAXN];
int i, j, m, n, c;
if (k == 1)
{
return (a[0][0]);
}
else
{
det = 0;
for (c = 0; c < k; c++)
{
m = 0;
n = 0;
for (i = 0;i < k; i++)
{
for (j = 0 ;j < k; j++)
{
b[i][j] = 0;
if (i != 0 && j != c)
{
b[m][n] = a[i][j];
if (n < (k - 2))
n++;
else
{
n = 0;
m++;
}
}
}
}
det = det + s * (a[0][c] * determinant(b, k - 1));
s = -1 * s;
}
}
return (det);
}
void cofactor(float num[MAXN][MAXN], float f,float c[MAXN][MAXN],float b1[][MAXN],float border)
{
float b[MAXN][MAXN], fac[MAXN][MAXN];
int p, q, m, n, i, j;
for (q = 0;q < f; q++)
{
for (p = 0;p < f; p++)
{
m = 0;
n = 0;
for (i = 0;i < f; i++)
{
for (j = 0;j < f; j++)
{
if (i != q && j != p)
{
b[m][n] = num[i][j];
if (n < (f - 2))
n++;
else
{
n = 0;
m++;
}
}
}
}
fac[q][p] = pow(-1, q + p) * determinant(b, f - 1);
}
}
transpose(num, fac, f,c,b1,border);
}
/*Finding transpose of matrix*/
void transpose(float num[MAXN][MAXN], float fac[MAXN][MAXN], float r,float atrans[MAXN][MAXN],float b1[][MAXN],float border)
{
int i, j;
float b[MAXN][MAXN], inverse[MAXN][MAXN], d;
for (i = 0;i < r; i++)
{
for (j = 0;j < r; j++)
{
b[i][j] = fac[j][i];
}
}
d = determinant(num, r);
for (i = 0;i < r; i++)
{
for (j = 0;j < r; j++)
{
inverse[i][j] = b[i][j] / d;
}
}
float midmul[MAXN][MAXN];
findmultiply(midmul,inverse,atrans,r,border,r);
float finalans[MAXN][MAXN];
findmultiply(finalans,midmul,b1,r,1,border);
for (int i=0;i<r;++i)
printf("%f\n",finalans[i][0]);
}