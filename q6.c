#include<stdio.h>
#include<math.h>
#include<stdlib.h>
void matrix_mul(float matrix1[3][3],float matrix2[3][1],float matrix3[3][1]){
int i,j,k;
for(i = 0; i < 3; i++){
for(j = 0; j < 1; j++){
matrix3[i][j] = 0;
for(k = 0; k < 3; k++){
matrix3[i][j] += matrix1[i][k]*matrix2[k][j];
}
}
}
}
float findmax(float array[3][1]){
int i;
float maximum;
maximum = array[0][0];
for(i = 0; i < 3; i++){
if(maximum < array[i][0])
maximum = array[i][0];
}
return maximum;
}
int isEqual(float matrix1[3][1], float matrix2[3][1]){
if(matrix1[0][0] == matrix2[0][0]
&& matrix1[1][0] == matrix2[1][0]
&& matrix1[2][0] == matrix2[2][0])
return 1;
return 0;
}
int main(){
float matrix1[3][3], matrix2[3][1],result[3][1];
float eigenValue;
int i,j,k;
printf("Enter 3x3 matrix:\n");
for(i = 0; i < 3; i++){
for(j = 0; j < 3; j++){
scanf("%f",&matrix1[i][j]);
}
}
for(i = 0; i < 3; i++){
for(j = 0; j < 1; j++){
matrix2[i][j] = 1.0;
}
}
while(1){
matrix_mul(matrix1,matrix2,result);
eigenValue = findmax(result);
for(i = 0; i < 3; i++){
result[i][0]/=eigenValue;
}
if(isEqual(matrix2,result)==1){
break;
}
for(i = 0; i < 3; i++){
matrix2[i][0] = result[i][0];
}
}
printf("Greatest Eigen Value = %f", eigenValue);
printf("\nAny one of Eigen Vector: \n");
for(i = 0; i < 3; i++){
for(j = 0; j < 1; j++){
printf("%.2f",result[i][j]);
printf("\t");
}
printf("\n");
}
return 0;
}