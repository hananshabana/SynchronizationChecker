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

   	int in_stvar(  int step,   int no_states ,  int ou_st_num, int in_st_num )
   	{

return(((no_states*no_states)*(step-1))+(no_states*ou_st_num)+(in_st_num+1));
  }
 
   
       int lettervar(  int step, int  no_states,   int totaltime)
       {
		 return(in_stvar(   totaltime,   no_states,  no_states-1 ,  no_states-1 ) +(step));
       }      
            
	  
	  int new_lettervar(  int z,   int no_states, int totaltime)
       {
        
          
         return (lettervar(  totaltime,   no_states,  totaltime)+ z+1);
     }
        
		 
      int fay(  int u1,   int no_states, int totaltime)
	  {
	  return(new_lettervar(no_states-1, no_states, totaltime)+u1+1);
	   } 
	     
int main()

{ 
unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
  std::default_random_engine generator (seed);


int n;
int lamda=2;
poisson_distribution<int> distribution (lamda);
uniform_int_distribution<int> dist_uniform(0,n-1);



 ofstream mean ("mean.txt");   
  if (mean.is_open())
  {
  
mean <<"   number of states=    "<<n<<endl;
}
for (int c=1;c<=1;c++)
{	

mean << "Ex_No=   "<<c<< "      ";

int shortest_length=0;
string yes="SAT";
string no="UNSAT";	

int mid, length;
         
int first;
int last;
	
std::vector <std::list <int> > out_a(n); std::vector <std::list <int> > out_b(n);

std::vector <std::list <int> > out_ax(n); std::vector <std::list <int> > out_bx(n);
  int random_integer_a; int random_integer_b; int random_state_a; int random_state_b; int  range_states;

struct f
	{
	int a;
	int b;
	};
	f s[n];
	



for (int fla=0; fla<=n-1;fla++)
{
out_a[fla].push_back(fla);
out_b[fla].push_back(fla);
out_ax[fla].push_back(fla);
out_bx[fla].push_back(fla);
}
 

 
 
 for (int sa=0;sa<=n-1; sa++)
{
gen:    
    int lowest=0, highest_c=n;
    int range_card=(highest_c-lowest)+1;     
    
	random_integer_a= distribution(generator)% n+1;
	random_integer_b= distribution(generator)% range_card;
		 s[sa].a=random_integer_a;
		 s[sa].b=random_integer_b;
		 
       

	   lowest=0; int highest_s=n-1; 
	 
	 
	 if (random_integer_b==0)
	{
	 out_b[sa].push_back(highest_s+1);

	}	 
     	 
	 int x[random_integer_a]; int y[random_integer_b]; 
    for(int index=0; index<random_integer_a; index++)
	{ 
    
           
		ha:
		random_state_a = dist_uniform(generator);
		x[index]=random_state_a;
		for(int k=0;k<index;k++)
		{if( x[index]==x[k])
		{goto ha;}
		}
		        out_a[sa].push_back(random_state_a); 
	   out_ax[random_state_a].push_back(sa);  
	   
	    
    }
	for(int index=0; index<random_integer_b; index++)
	{ 
             
		dd:
		random_state_b = dist_uniform(generator);
		y[index]=random_state_b;
		for(int l=0;l<index;l++)
		{if( y[index]==y[l])
		{goto dd;}}
        out_b[sa].push_back(random_state_b); 
	   out_bx[random_state_b].push_back(sa);
	 }
	 }
 int mn1,mn2;

  for(std::vector < std::list <int> > :: iterator rp_a = out_ax.begin();  rp_a!= out_ax.end()  ; rp_a++)
{        
std::list <int>  r1_p=*rp_a;  
std::list <int>  ::iterator r2_p=r1_p.begin();
mn1=(*r2_p);
r2_p++;
if(r2_p==r1_p.end())
{
out_ax[mn1].push_back(n);
}}

////////////////////////////////////////////////

for(std::vector < std::list <int> > :: iterator rp_b = out_bx.begin();  rp_b!= out_bx.end()  ; rp_b++)
{

        
  	std::list <int>  r1_pb=*rp_b;  
std::list <int>  ::iterator r2_pb=r1_pb.begin();
mn2=(*r2_pb);
r2_pb++;
if(r2_pb==r1_pb.end())
{
out_bx[mn2].push_back(n);
}
}
////////////////////////////////////////////////
while((first < last))
{

	mid = (last+first)/2;
     
	length =mid;

int sum_cla=0; 
int sum_clb=0;  
int clauses_a;  
int clauses_b;
  
for(std::vector < std::list <int> > :: iterator iv_a = out_a.begin();  iv_a!= out_a.end()  ; iv_a++)
    {
        
  	std::list <int>  i1v_a=*iv_a;  
 	

for(std::list <int> ::iterator i2v_a=i1v_a.begin();  i2v_a != i1v_a.end(); i2v_a++) {



sum_cla =sum_cla+1;


} sum_cla--;      
}
clauses_a=((sum_cla )*n);


/////////////////////////////////////////////////////////////////////////////////////

for(std::vector < std::list <int> > :: iterator iv_b = out_b.begin();  iv_b!= out_b.end()  ; iv_b++)
    {
        
  	std::list <int>  i1v_b=*iv_b;  
 	

for(std::list <int> ::iterator i2v_b=i1v_b.begin();  i2v_b != i1v_b.end(); i2v_b++) {

sum_clb =sum_clb+1;

}sum_clb--;
}
clauses_b=((sum_clb )*n);


////// ///////////////////////////

int kbxs,kaxs; 
int sum_clau_r=0;

std::vector < std::list <int> > :: iterator i_axs = out_ax.begin();

for(std::vector < std::list <int> > :: iterator i_bxs = out_bx.begin();  i_bxs!= out_bx.end()  ; i_bxs++)
    {

  	std::list <int>  i1_bxs=*i_bxs;  
std::list <int>  ::iterator i2_bxs=i1_bxs.begin();

 kbxs=(*i2_bxs);

i2_bxs++;
	
	if ((*i2_bxs)!=n)
	{
	
	std::list <int>  i1_axs=*i_axs;  
std::list <int>  ::iterator i2_axs=i1_axs.begin();

 kaxs=(*i2_axs);

i2_axs++;

if ((*i2_axs)==n)
	{sum_clau_r=sum_clau_r+2;}  

else
{
sum_clau_r=sum_clau_r+3;
}}
else if ((*i2_bxs)==n)
{
std::list <int>  i11_axs=*i_axs;  
std::list <int>  ::iterator i22_axs=i11_axs.begin();
 kaxs=(*i22_axs);
i22_axs++;

if ((*i22_axs)==n)
	{sum_clau_r=sum_clau_r+1;}  
	
else if((*i22_axs)!=n) 
{sum_clau_r=sum_clau_r+2;}}
i_axs++;}

/////////////////////////////////////////////////////////////////////////////
int fi_a=0;  int fi_b=0; int s1,s2;int fi_a1;  int fi_b1;

for(std::vector < std::list <int> > :: iterator iv_bf = out_b.begin();  iv_bf!= out_b.end()  ; iv_bf++)
    {

        
  	std::list <int>  i1v_bf=*iv_bf;  
 	
	std::list <int> ::iterator i2v_bf=i1v_bf.begin();
s2=(*i2v_bf);
i2v_bf++;
for(  ;i2v_bf != i1v_bf.end(); i2v_bf++) {
if((*i2v_bf)==n)
{fi_b++;}
}}
fi_b1=fi_b;


int yy;
if((fi_b1>0)||(fi_a1>0))
 {yy=1;}
 else 
 {yy=0;}
 
//////////////////////////////////////////////////////////////////////////////////

   ofstream myfile ("inf.txt");
  if (myfile.is_open())
  { 
     int variables_no;
  if (length>1)
 {
  variables_no= new_lettervar(  n-1,   n, length)+yy+1;}
 
 if (length==1)
 {
  variables_no= new_lettervar(  n-1,   n, length)+1;}
  
  
  
     
     int clauses_no= ((clauses_a+clauses_b)*(length))+((n*n)+1)+(n)+((sum_clau_r*n)*length)+((n*n))+1;
    
 myfile<< endl<<" p cnf "  <<variables_no<< "  "<<clauses_no << endl;




////////////////////////////////////////////////////////////////////////////////////////////////



int ka;
for (int t_a=1; t_a<= length-1; t_a++)
   {

for(std::vector < std::list <int> > :: iterator i_a = out_a.begin();  i_a!= out_a.end()  ; i_a++)
    {
  	std::list <int>  i1_a=*i_a;  
std::list <int>  ::iterator i2_a=i1_a.begin();


ka=(*i2_a);

i2_a++;
for( ; i2_a != i1_a.end(); i2_a++) 
   {
	for(int va=0; va<=n-1; va++)
	{	
myfile<<"-"<<in_stvar(  t_a,   n ,va ,  ka )<<"   ";
	myfile<<"-"<<lettervar(  t_a+1, n,   length)<<"   ";
	myfile<<in_stvar(  t_a+1,   n ,va, (*i2_a) )<< "  "<<"0"<<endl;
	} 
   }
  }

 }

  ////////////////////////////////////////////////////////////////

int kb;
for (int t_b=1; t_b<= length-1; t_b++)
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
	
	
	for(int vb=0; vb<=n-1; vb++){	
     myfile<<"-"<<in_stvar(  t_b,   n ,vb ,  kb )<<"   ";
	myfile<<lettervar(  t_b+1, n,   length)<<"   ";
	myfile<<in_stvar(  t_b+1,   n ,vb, (*i2_b) )<< "  "<<"0"<<endl;
	} 
	}
	
else
   {
	for(int vb=0; vb<=n-1; vb++){	
myfile<<"-"<<in_stvar(  t_b,   n ,vb ,  kb )<<"   ";
	myfile<<lettervar(  t_b+1, n,   length)<<"   ";
	myfile<<fay(  1,   n, length)<< "  "<<"0"<<endl;
	} 
	}
	
   } 
  }

 }


 //////////////////////////////////////////////////////////////////////////////
 
  
   int kbx;
for (int t_bx=1; t_bx<= length-1; t_bx++)
   {


std::vector < std::list <int> > :: iterator i_ax = out_ax.begin();

for(std::vector < std::list <int> > :: iterator i_bx = out_bx.begin();  i_bx!= out_bx.end()  ; i_bx++)
    {
     
  	std::list <int>  i1_bx=*i_bx;  
std::list <int>  ::iterator i2_bx=i1_bx.begin();

kbx=(*i2_bx);

i2_bx++;

	
	if ((*i2_bx)!=n)
	{
	
	std::list <int>  i1_ax=*i_ax;  
std::list <int>  ::iterator i2_ax=i1_ax.begin();

int kax=(*i2_ax);

i2_ax++;

if ((*i2_ax)!=n)
	{ 
	
for(int vbx=0; vbx<=n-1; vbx++)
   {
	myfile<<"-"<<in_stvar(  t_bx+1,   n , vbx, kbx )<<"  ";
	i2_bx=i1_bx.begin();
	
	i2_bx++;
for( ; i2_bx != i1_bx.end(); i2_bx++) {
			
myfile<<in_stvar(  t_bx,   n , vbx, (*i2_bx) )<<"  ";
}
myfile<<lettervar( t_bx+1, n,  length)<<"   "<<"0"<<endl;

  
  
  ////////////////////////////////////////////////////////////////
  
  std::list <int>  i1_ax=*i_ax;  
   std::list <int>  ::iterator i2_ax=i1_ax.begin();

    kax=(*i2_ax);
 
   i2_ax++;

	myfile<<"-"<<in_stvar(  t_bx+1,   n , vbx, kax )<<"  ";
	i2_ax=i1_ax.begin();
	i2_ax++;
 for( ; i2_ax != i1_ax.end(); i2_ax++) {
			
   myfile<<in_stvar(  t_bx,   n , vbx, (*i2_ax) )<<"  ";
}
  myfile<<"-"<<lettervar( t_bx+1, n,  length)<<"   "<<"0"<<endl;


	myfile<<"-"<<in_stvar(  t_bx+1,   n , vbx, kbx )<<"   ";
	i2_bx=i1_bx.begin();
	i2_bx++;
	for(; i2_bx != i1_bx.end(); i2_bx++) {
			
myfile<<in_stvar(  t_bx,   n , vbx, (*i2_bx) )<<"  ";}

i2_ax=i1_ax.begin();
	i2_ax++;
for(; i2_ax != i1_ax.end(); i2_ax++) {
			
myfile<<in_stvar(  t_bx,   n , vbx, (*i2_ax) )<<"  ";}
myfile<<"   "<<"0"<<endl;
}}} i_ax++;}}


	
////////////////////////////////////////////////////////////////////////
	
	int kbxa; int kaxa; int kbxb; int kbxb2;  
	int kaxb2;
for (int t_bxb1=1; t_bxb1<= length-1; t_bxb1++)
   {


std::vector < std::list <int> > :: iterator i_axb1 = out_bx.begin();

for(std::vector < std::list <int> > :: iterator i_bxb1 = out_ax.begin();  i_bxb1!= out_ax.end()  ; i_bxb1++)
    {

  	std::list <int>  i1_bxb1=*i_bxb1;  
std::list <int>  ::iterator i2_bxb1=i1_bxb1.begin();

  kbxb2=(*i2_bxb1);

i2_bxb1++;

	
	if ((*i2_bxb1)!=n)
	{
	
	std::list <int>  i1_axb1=*i_axb1;  
std::list <int>  ::iterator i2_axb1=i1_axb1.begin();

kaxb2=(*i2_axb1);


i2_axb1++;

if ((*i2_axb1)==n)
	{  	

	
for(int vbxb1=0; vbxb1<=n-1; vbxb1++)
   {
	i2_bxb1=i1_bxb1.begin();
	i2_bxb1++;
	
	myfile<<"-"<<in_stvar(  t_bxb1+1,   n , vbxb1, kbxb2 )<<"  ";
for( ; i2_bxb1 != i1_bxb1.end(); i2_bxb1++) {
			
myfile<<in_stvar(  t_bxb1,   n , vbxb1, (*i2_bxb1) )<<"  ";

}myfile<<"   "<<"0"<<endl;
myfile<<"-"<<in_stvar(  t_bxb1+1,   n , vbxb1, kbxb2 )<<"  "<<lettervar( t_bxb1+1, n,  length)<<"   "<<"0"<<endl;}
}}i_axb1++;}}
	

///////////////////////////////////////////////////////////////////////////////////////////
  
  
  
	int kaxb;
for (int t_bxb=1; t_bxb<= length-1; t_bxb++)
   {

std::vector < std::list <int> > :: iterator i_axb = out_ax.begin();

for(std::vector < std::list <int> > :: iterator i_bxb = out_bx.begin();  i_bxb!= out_bx.end()  ; i_bxb++)
    {

  	std::list <int>  i1_bxb=*i_bxb;  
std::list <int>  ::iterator i2_bxb=i1_bxb.begin();

kbxb=(*i2_bxb);

i2_bxb++;

	if ((*i2_bxb)!=n)
	{
	
	std::list <int>  i1_axb=*i_axb;  
std::list <int>  ::iterator i2_axb=i1_axb.begin();

kaxb=(*i2_axb);

i2_axb++;

if ((*i2_axb)==n)
	{    
  
	
for(int vbxb=0; vbxb<=n-1; vbxb++)
   {
	i2_bxb=i1_bxb.begin();
	i2_bxb++;
	
	myfile<<"-"<<in_stvar(  t_bxb+1,   n , vbxb, kbxb )<<"  ";
for( ; i2_bxb != i1_bxb.end(); i2_bxb++) {
			
myfile<<in_stvar(  t_bxb,   n , vbxb, (*i2_bxb) )<<"  ";

}myfile<<"   "<<"0"<<endl;
myfile<<"-"<<in_stvar(  t_bxb+1,   n , vbxb, kbxb )<<"  "<<"-"<<lettervar( t_bxb+1, n,  length)<<"   "<<"0"<<endl;}
}}i_axb++;}}

///////////////////////////////////////////////////////////////////	
	  

	 	
	int kbxa3; int kaxa3; int kbxb3;
for (int t_axa3=1; t_axa3<= length-1; t_axa3++)
   {


std::vector < std::list <int> > :: iterator i_bxa3 = out_bx.begin();

for(std::vector < std::list <int> > :: iterator i_axa3 = out_ax.begin();  i_axa3!= out_ax.end()  ; i_axa3++)
    {

  	std::list <int>  i1_axa3=*i_axa3;  
std::list <int>  ::iterator i2_axa3=i1_axa3.begin();

kaxa3=(*i2_axa3);

i2_axa3++;
	
	if ((*i2_axa3)==n)
	{
	
	std::list <int>  i1_bxa3=*i_bxa3;  
std::list <int>  ::iterator i2_bxa3=i1_bxa3.begin();

kbxa3=(*i2_bxa3);

i2_bxa3++;

if ((*i2_bxa3)==n)
	{ 	
for(int vaxa3=0; vaxa3<=n-1; vaxa3++)
   {	
	myfile<<"-"<<in_stvar(  t_axa3+1,   n , vaxa3, kaxa3 )<<"  "<<"0"<<endl;
}

}}i_bxa3++;}}
	
	/////////////////////////////////////////////////////
	myfile<<"-"<<fay(  0,   n, length)<< "  "<<"0"<<endl;
	
  
  ////////////////////////////////////////////////////////
  
  
  for(int w=0; w<=n-1; w++)
  
  {myfile<<new_lettervar(  w,   n, length)	<<"   ";
   	
  }myfile<<"0"<< endl;
 
 
 
 ///////////////////////////////////////////////////////////////
  
for(int p=0; p<=n-1; p++){
 	
 for(int p1=0; p1<=n-1; p1++){
 	
 	myfile<<"-"<<new_lettervar(  p,   n, length)<<"  ";	
 		
   myfile<<in_stvar(length ,n, p1,p)<<"  "<<" 0"<<endl;
}}

 /////////////////////////////////////////////

for(int q=0; q<=n-1; q++){
 	myfile<<new_lettervar(  q,   n, length)<<"  ";
 for(int q1=0; q1<=n-1; q1++){
 	 		
   myfile<<"-"<<in_stvar(length ,n, q1,q)<<"  ";
}myfile<<" 0"<<endl;}


// ////////////////////////////////////////////////////////////////////

myfile<<lettervar(  1, n,   length)<<"   "<<"0"<<endl;
int k0;


//////////////////////////////////////////////////

for(std::vector < std::list <int> > :: iterator i_a = out_a.begin();  i_a!= out_a.end()  ; i_a++)
    {

       
  	std::list <int>  i1_a=*i_a;  
std::list <int>  ::iterator i2_a=i1_a.begin();
k0=(*i2_a);

i2_a++;

for( ; i2_a != i1_a.end(); i2_a++) {
		
	myfile<<in_stvar(  1,   n , k0 ,(*i2_a) )<< "  "<<"0"<<endl;

}

}


 ///////////////////////////////////////////////////

for(std::vector < std::list <int> > :: iterator i_a = out_a.begin();  i_a!= out_a.end()  ; i_a++)
    {

        
  	std::list <int>  i1_a=*i_a;  
std::list <int>  ::iterator i2_a=i1_a.begin();
k0=(*i2_a);


i2_a++;
 

  for (int th=0;th<=n-1;th++)	
{	
	int check=0;	

for( ; i2_a != i1_a.end(); i2_a++) 
{
	if((*i2_a)==th )
	{check=1;
	break;
	}
}
if(check==0)
{
		myfile<<"-"<<in_stvar(  1,   n , k0 ,th )<< "  "<<"0"<<endl;}
		
		
		i2_a=i1_a.begin();
	i2_a++;
	}
}


 /////////////////////////////////////////////////////////////////////
 myfile.close();}
 
else
 {
myfile<<"un able to open  file of cnf formula (inf.txt)";}
 
	   

system("minisat  inf.txt  ouf.txt");

string word;
	
	ifstream outfile;
	outfile.open("ouf.txt");
	
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
	outfile.close();	 
	} 
	

 
else cout << "Unable to open ouf file.";	
      


 }mean << " the shortest_length is   "<<shortest_length<<endl;


 
}

mean.close();


return(0);
}
