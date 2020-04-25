#include <stdio.h>
#include<stdlib.h>
#include<math.h>
#include<time.h>
int R,C;
void swap(int *mat, int row1, int row2,int col)
{
for (int i = 0; i < col; i++)
{
int temp = *(mat+row1*C+i);
*(mat+row1*C+i) = *(mat+row2*C+i);
*(mat+row2*C+i) = temp;
}
}
int rankOfMatrix(int *mat,int *a)
{
int rank = C;
for (int row = 0; row < rank; row++)
{
if (*(mat+row*C+row))
{
for (int col = 0; col < R; col++)
{
if (col != row)
{
double mult =(double)(*(mat+col*C+row)) / (*(mat+row*C+row));
for (int i = 0;i < rank; i++)
*(mat+col*C+i) -= mult * (*(mat+row*C+i));
}
}
}
else
{
int reduce = 1;
for (int i = row + 1; i < R; i++)
{
if (*(mat+i*C+row))
{
swap(mat, row, i,rank);
reduce = 0;
break ;
}
}
if (reduce)
{
a[row]=-1;
rank--;
for (int i = 0; i < R; i++)
*(mat+i*C+row) = *(mat+i*C+rank);
}
row--;
}
}
return rank;
}
void display(int *mat, int row, int col)
{
for (int i = 0; i < row; i++)
{ for (int j = 0; j < col; j++)
printf(" %d", *(mat+i*C+j));
printf("\n");
}
}
void printbasis(int *mat,int *a,int x)
{
printf("Basis for the given matrix\n");
for(int j=0;j<x;j++)
{printf("( ");
if(a[j]!=-1)
{
for(int i=0;i<R;i++)
{
printf("%d",*(mat+i*C+j));
}
}
printf(")");
printf("\n");
}
}
int main()
{
clock_t start,end;
printf("Enter the number of rows:\n");
scanf("%d",&R);
printf("Enter the number of columns:\n");
scanf("%d",&C);
int *mat=malloc(sizeof(int)*R*C);
int *mat1=malloc(sizeof(int)*R*C);
for(int i=0;i<R;i++)
for(int j=0;j<C;j++)
{
*(mat+i*C+j)=rand();
*(mat1+i*C+j)=*(mat+i*C+j);
}
int x;
if(R<C)
x=R;
else
x=C;
int *a=malloc(sizeof(int)*x);
for(int i=0;i<x;i++)
a[i]=1;
start=clock();
int rank=rankOfMatrix(mat,a);
if(rank>x)
rank=x;
printf("\n");
end=clock();
if (R<11)
printbasis(mat1,a,x);
printf("%d is the dimension .\n",rank);
printf("The time taken for this execution is %lf\n",((double)(end-start))/CLOCKS_PER_SEC);
return 0;
}