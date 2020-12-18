/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include <iostream>
#include "properties.hpp"
#include "print.hpp"
#include "operations.hpp"
#include "esop.hpp"
#include "implicant.hpp"
#include <string>
using namespace std;
namespace kitty
{

// This function will convert decimal to binary
// This will help with the constraints and the
// minterms. From the minterm '7' eg I want to see
// which variables are on ONSET. So I have to convert
// to binary first.
std::string convertDecimalToBinary(int n)
{
    /* If the minterm = 0 then I cannot implement*/
    /* the constraints. As the binary will be '0'*/
    // which means all the rest variables will not
    // be taken into account. So, I do it like this
    /* considering max variables = 16... */
    if (n==0) {return "0000000000000000";}
    long long binaryNumber = 0;
    int remainder, i = 1, step = 1;
    while (n!=0)
    {
        remainder = n%2;
        n /= 2;
        binaryNumber += remainder*i;
        i *= 10;
    }
    string stringBinary = to_string(binaryNumber);
    return stringBinary;
}
/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  std::vector<int64_t> neg_unate_vec;


  /* TODO ************ */
   
  //cout << "Truth table is :" << to_binary(tt) << endl;
  auto my_tt = tt;
  // For each variable check if positive or negative unateness
  // If negative unate, then flip
  for ( auto i = 0u; i< my_tt.num_vars(); i++)  {
  	auto pos_cofactor = cofactor1(my_tt, i );
  	auto neg_cofactor = cofactor0(my_tt, i );
  	auto pos_unate = binary_or(unary_not(neg_cofactor), pos_cofactor);
   	auto neg_unate = binary_or(unary_not(pos_cofactor), neg_cofactor);
  	if (count_ones(pos_unate) != pos_unate.num_bits() && count_ones(neg_unate) != neg_unate.num_bits()) {	  
		std::cout << "It is binate!" << std::endl;
		return false;
 	 }
 	else {
		if (count_ones(neg_unate) == neg_unate.num_bits()){
			neg_unate_vec.push_back(i);
			my_tt = flip(tt, i);		
	     }
		continue;	
 	 }
  }


// ILP Solver
  lprec *lp;
  int Ncol, *colno = NULL, j, ret = 0;
  REAL *row = NULL;

  Ncol = my_tt.num_vars() + 1; 
  lp = make_lp(0, Ncol);
  if(lp == NULL)
  	ret = 1; /* couldn't construct a new model... */
  if(ret == 0) {
    /* let us name our variables. Not required, but can be useful for debugging */
   	 for ( int i = 1; i <= Ncol - 1; i++){
    	 	std::string char1 = "w";
    		char1 = char1 + std::to_string(i);
    		char *charf = &char1[0]; 
   		 set_col_name(lp, i, charf);
        	   if ( i == Ncol - 1) {
		  	 set_col_name(lp, i + 1, "T");
		  	 break;
	  	   }
 	  }  
       	  colno = (int *) malloc(Ncol * sizeof(*colno) + 200);
    	  row = (REAL *) malloc(Ncol * sizeof(*row) + 200);
          if((colno == NULL) || (row == NULL))
      	  	ret = 2; 
  }
  // Here we construct the constraints regarding the ONSET
  if(ret == 0) {
  	set_add_rowmode(lp, TRUE);  /* makes building the model faster if it is done rows by row */
	auto minterms = get_minterms(my_tt);
        for (int i = 0; i<minterms.size(); i++) {
        	auto minterm1 = minterms.at(i);
		auto binary_minterm = convertDecimalToBinary(minterm1);  
    		j = 0;
    		for ( int z = 0; z < binary_minterm.size(); z++){	
			if ( binary_minterm[binary_minterm.size()-1-z] == '1'){
	 			colno[j] = z + 1;
				row[j++] = 1;
	
			}
			else {			
				colno[j] = z + 1;
				row[j++] = 0;
			}
  		 }		   
    	 	colno[j] = Ncol;
	 	row[j++] = -1;
    	 	if(!add_constraintex(lp, j, row, colno, GE, 0))
     	 		ret = 3;
 	 }
  }

  // Here we construct the constraints regarding the OFFSET
  if(ret == 0) {
  	set_add_rowmode(lp, TRUE);  /* makes building the model faster if it is done rows by row */
   	auto neg_tt = unary_not(my_tt);
    	auto minterms = get_minterms(neg_tt);     
        for (int i = 0; i<minterms.size(); i++){
       		auto minterm1 = minterms.at(i);
    		auto binary_minterm = convertDecimalToBinary(minterm1);   
   		j = 0;  
    		for ( int z = 0; z < binary_minterm.size(); z++){	 
			if ( binary_minterm[binary_minterm.size()-1-z] == '1'){
	        		colno[j] = z + 1;
	 			row[j++] = 1;
			}
			else {	
				colno[j] = z + 1;
				row[j++] = 0;
			}
	   	 }   
        	 colno[j] = Ncol;
	 	 row[j++] = -1;
    	 	 if(!add_constraintex(lp, j, row, colno, LE, - 1))
     	 	 	ret = 3;
  	}
  }


 /* Here we construct the rest of constraints => all variables & T >= 0 */
 if(ret == 0) {
 	set_add_rowmode(lp, TRUE); 
    	for ( int z = 0; z < Ncol; z++){	 
	 	j=0;
	 	colno[j] = z+1;
	 	row[j++] = 1;
	 	if(!add_constraintex(lp, j, row, colno, GE, 0))
     	 		ret = 3;
    	}
 }


  

  // Here we set the objective
  if(ret == 0) {
  	set_add_rowmode(lp, FALSE); /* rowmode should be turned off again when done building the model */
    	/* set the objective function */
    	j = 0;
	for ( int z = 0; z < Ncol; z++){	 
		colno[j] = z+1;
	 	row[j++] = 1;
	}
       /* set the objective in lpsolve */
        if(!set_obj_fnex(lp, j, row, colno))
        	ret = 4;
  }

   // Here we solve and calculate the solution (if feasible)
   if(ret == 0) {
       	set_minim(lp); /* set the object direction to minimize */
       	//write_LP(lp, stdout); /* Show the model in lp format on screen 
	set_verbose(lp, IMPORTANT); /* I only want to see important messages on screen while solving */
	ret = solve(lp);  /* Now let lpsolve calculate a solution */
	if(ret == OPTIMAL)
     		 ret = 0;
   	else
      		 ret = 5;
   }
  


    if (ret == 5) {return false;} /* It is infeasible, so return False*/
    if(ret == 0) {
    /* a solution is calculated, now lets get some results */
    	printf("Objective value: %f\n", get_objective(lp)); /* objective value */
    /* variable values. Also pass them to the vector! */
    	get_variables(lp, row);
    	for(j = 0; j < Ncol; j++){ 
		//printf("%s: %f\n", get_col_name(lp, j + 1), row[j]); 
		linear_form.push_back(round(row[j]));
   	 }
    }
 
    
  /* free allocated memory */
  if(row != NULL)
  	free(row);
  if(colno != NULL)
    	free(colno);

  if(lp != NULL) {
    /* clean up such that all used memory by lpsolve is freed */
    	delete_lp(lp);
  } 

  /*Trasform the linear form into the appropriate one*/
  for (auto i : neg_unate_vec){	  
	  linear_form.at(i) = -linear_form.at(i);
	  linear_form.at(tt.num_vars()) = linear_form.at(tt.num_vars()) + linear_form.at(i);
  }
  
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf ){
    	 *plf = linear_form;
  }

  return true;
}
} /* namespace kitty */
