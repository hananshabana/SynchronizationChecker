#include <iostream>
#include<vector>
#include<list>
#include <fstream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
 #include<string>
#include<ctime>
#include <chrono>
#include <random>
using namespace std;




 int input_state( int  input_stateno , int step,   int no_states)
     {
       return(no_states*(step-1)+(input_stateno+1));
     }
   /////////////////////////////////////////////////////
 int lettervar(  int step, int  no_states,   int totaltime)
     {
          
		 return (input_state( no_states-1 , totaltime,   no_states) +(step-1));
    }
       
        ///////////////////////////////////////////
 int fay(  int u1,   int no_states, int totaltime)
	{
	  return(lettervar( totaltime,no_states, totaltime)+u1+1);} 
 
int main()

{
 
  const std::mt19937::result_type seed = std::random_device{}();

		std::mt19937 eng{seed};
 

int n; //number of states
int n_EX; // number of  automata

uniform_int_distribution<int> dist_uniform(0,n-1);
///////////////////////////////////////////////


 ofstream result ("result.txt");   
  if (result.is_open())
  {
  
result <<"   number of states=    "<<n<<endl;
}
for (int c=1;c<=n_EX;c++)
{	

result << "Ex_No=   "<<c<< "      ";	

int shortest_length=0;

///////////////////

int mid, length;
  
       
int first; // min length
int last ;  // max length


///////////////////////////////////	


std::vector <std::list <int> > out_a(n); std::vector <std::list <int> > out_b(n);   

for (int fla=0; fla<=n-1;fla++)
{
out_a[fla].push_back(fla);
out_b[fla].push_back(fla);

}
 

 
 int image[2*n];
 
 int undst1=dist_uniform(eng); 
 out_b[undst1].push_back(n); 
 for(int g=0;g<=(2*n)-1;g++)
 {
 
 image[g]=dist_uniform(eng);
 }
 for(int ga=0;ga<=n-1;ga++)
 {out_a[ga].push_back(image[ga]);}
 
 for(int gb=0;gb<=n-1;gb++)
 {
 if(gb==undst1)
 
 {cout<<"undefined tansition for b at"<<"   "<<undst1;}
 else 
 { 
 out_b[gb].push_back(image[n+gb]);}
}


////////////////////////////////////////////// CNF creating  ////////////////////
while(first < last)
{
	
	
	  	
	  	mid = (first+last)/2;

       length =mid;  

     
   int sum_cla=0; int sum_clb=0;  
 int clauses_a;  int clauses_b;
 // caluate number of clauses for a
 
for(std::vector < std::list <int> > :: iterator iv_a = out_a.begin();  iv_a!= out_a.end()  ; iv_a++)
    {

        
  	std::list <int>  i1v_a=*iv_a;  
 	
	

for(std::list <int> ::iterator i2v_a=i1v_a.begin();  i2v_a != i1v_a.end(); i2v_a++) {



sum_cla =sum_cla+1;


} sum_cla--;      
}
clauses_a=((sum_cla ));


for(std::vector < std::list <int> > :: iterator iv_b = out_b.begin();  iv_b!= out_b.end()  ; iv_b++)
    {        
  	std::list <int>  i1v_b=*iv_b; 	

for(std::list <int> ::iterator i2v_b=i1v_b.begin();  i2v_b != i1v_b.end(); i2v_b++) 
{

sum_clb =sum_clb+1;

}sum_clb--;
}

clauses_b=((sum_clb ));   
       
  
   ofstream myfile ("in.txt");
  
  if (myfile.is_open())
  { 
 
 int variables_no=  lettervar(length+1, n, length+1)+1;
  
     
     int clauses_no=((n*(n-1))/2)+((clauses_b+clauses_a)*length)+n+2;  
    
 myfile<< " p cnf "  <<variables_no<< "  "<<clauses_no << endl;



int ka;
for (int t_a=1; t_a<= length; t_a++)
   {





for(std::vector < std::list <int> > :: iterator i_a = out_a.begin();  i_a!= out_a.end()  ; i_a++)
    {       
  	std::list <int>  i1_a=*i_a;  
std::list <int>  ::iterator i2_a=i1_a.begin();

ka=(*i2_a);


i2_a++; 	
	
for( ; i2_a != i1_a.end(); i2_a++) {
	
if((*i2_a)!=n)
{

myfile<<"-"<<input_state( ka , t_a,   n)<<"  ";

	myfile<<"-"<<lettervar(  t_a+1, n,   length+1)<<"   ";
	myfile<<input_state( (*i2_a) , t_a+1,   n)<< "  "<<"0"<<endl;
}
}
}}


int kb;
for (int t_b=1; t_b<= length; t_b++)
   {

for(std::vector < std::list <int> > :: iterator i_b = out_b.begin();  i_b!= out_b.end()  ; i_b++)
    {

        
  	std::list <int>  i1_b=*i_b;  
std::list <int>  ::iterator i2_b=i1_b.begin();

kb=(*i2_b);

i2_b++;

for( ; i2_b != i1_b.end(); i2_b++) {
	
	if ((*i2_b)!=n)
	{
		
myfile<<"-"<<input_state( kb , t_b,   n)<<"   ";
	myfile<<lettervar(  t_b+1, n,   length+1)<<"   ";
	myfile<< input_state( (*i2_b) , t_b+1,   n)<< "  "<<"0"<<endl;	
	
	}	
	
	else
	{
	myfile<<"-"<<input_state( kb , t_b,   n)<<"   ";

	myfile<<lettervar(  t_b+1, n,   length+1)<<"   ";
	myfile<<fay(  0,   n, length+1)<< "  "<<"0"<<endl;
	}	
}

}

}
///////////////////////////////////// 
  
  for(int w=0; w<=n-1; w++)
  
  {
  
  myfile<<input_state( w , length+1,   n)	<<"   ";
   	
  }myfile<<"0"<< endl;
 
 
 
 ///////////////////////////////////////////////////////////////
 
 
for(int p=0; p<=n-1; p++){
 	
 for(int p1=0; p1<p; p1++){
 	
 	myfile<<"-"<<input_state( p , length+1,   n)<<"  "<<"-"<<input_state( p1 , length+1,   n)<<"  "<<" 0"<<endl;	
 		
   
}}
myfile<<endl;
  
  myfile<<"-"<<fay(  0,   n, length+1)<< "  "<<"0"<<endl;

////////////////////////////////
for(int s2=0; s2<=n-1; s2++)
{
myfile<<input_state( s2 , 1,   n)<<"   "<<" 0 "<<endl;

}

///////////////////////////////////////////////////////////////////////////////
 

 myfile.close();
 }

else
 {
myfile<<"un able to open  file of cnf formula (in.txt)";}
 

    
// invoke sat solver	   

system("minisat  xh.txt  out.txt");

/////////binary search///////////////////////////
string word;
	
	ifstream outfile;
	outfile.open("out.txt");
	
	if (outfile.is_open())
	
	{
	outfile>>word;
	if (word=="SAT")		
	
	{
	shortest_length=mid;
          
		  cout<<"sat with length = "<<shortest_length<<endl;
		   
		  last =mid;}
		  
		if (word=="UNSAT")
		{
		cout<<"not sat with length = "<<mid<<endl;
		first = mid+1;
		}
	outfile.close();	 }  
    
 
else cout << "Unable to open ouq file.";   
 }
 result << " the shortest_length is   "<<shortest_length<<endl;

}



result.close();


return(0);
}
