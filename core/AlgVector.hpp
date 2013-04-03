/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 *    AlgVector.cpp
 *    Copyright (C) 2002 University of Waikato, Hamilton, New Zealand
 *
 */

#include "RevisionHandler.hpp"
#include "Instances.hpp"
#include <stdlib.h> 

using namespace std;
// package weka.core;

// import java.io.Serializable;
// import java.util.Random;

/**
 * Class for performing operations on an algebraic vector
 * of floating-point values.
 *
 * @author  Gabi Schmidberger (gabi@cs.waikato.ac.nz)
 * @version $Revision: 1.10 $
 */
class AlgVector : /*public Cloneable,*/
		  /**public Serializable, */
		  public RevisionHandler {

  /** The values of the matrix */
  double *m_Elements;
  int m_numElements; 

  // vector<double> m_Elements; 

public:
  /**
   * Constructs a vector and initializes it with default values.
   *
   * @param n 		the number of elements
   */
  AlgVector(int n) {

    m_Elements = new double[n];
    initialize(false);
  }

  // copy constructor. 
  AlgVector Algvector(const AlgVector& vect); 

 /**
   * Constructs a vector using a given array.
   *
   * @param array 	the values of the matrix
   */
  AlgVector(vector<double> array); 

  /**
   * Constructs a vector using a given data format.
   * The vector has an element for each numerical attribute.
   * The other attributes (nominal, string) are ignored.
   * Random is used to initialize the attributes.
   *
   * @param format 	the data format to use
   * @param random 	for initializing the attributes
   * @throws Exception	if something goes wrong
   */
  //AlgVector(Instances format, Random random) throw(Exception);
  AlgVector(Instances format);

  /**
   * Constructs a vector using an instance.
   * The vector has an element for each numerical attribute.
   * The other attributes (nominal, string) are ignored.
   *
   * @param instance 	with numeric attributes, that AlgVector gets build from
   * @throws Exception 	if instance doesn't have access to the data format or
   * 			no numeric attributes in the data
   */
  // AlgVector(Instance instance) throw(Exception);
  AlgVector(Instance instance);

protected:
  void initialize(bool isRand);

public:
  const double getElement(int index) {
    return m_Elements[index];
  }

  const int numElements() {
  
    return m_Elements.length;
  }

  const void setElement(int index, double value) {
    
    m_Elements[index] = value;
  }

  /**
   * Sets the elements of the vector to values of the given array.
   * Performs a deep copy.
   *
   * @param elements 	an array of doubles
   */
  // const void setElements(double[] elements) {
  const void setElements(double elements[], int cnt) {

    for (int i = 0; i < cnt; i++) {
      m_Elements[i] = elements[i];
    }
  }
  
  /**
   * Gets the elements of the vector and returns them as double array.
   *
   * @return 		an array of doubles
   */
  //  double[] getElements(); 
  double * getElements(); 

  /**
   * Gets the elements of the vector as an instance.
   * !! NON-numeric data is ignored sofar
   * 
   * @param model 	the dataset structure to fit the data to
   * @param random 	in case of nominal values a random label is taken
   * @return 		an array of doubles
   * @throws Exception	if length of vector is not number of numerical attributes
   */
  // Instance getAsInstance(Instances model, Random random) throw(Exception); 
  Instance getAsInstance(Instances model); 
    
  /**
   * Returns the sum of this vector with another.
   *
   * @param other 	the vector to add
   * @return 		a vector containing the sum.
   */
  const AlgVector add(AlgVector other);

  /**
   * Returns the difference of this vector minus another.
   *
   * @param other 	the vector to subtract
   * @return 		a vector containing the difference vector.
   */
  const AlgVector substract(AlgVector other); 
 
  /**
   * Returns the inner (or dot) product of two vectors
   *
   * @param b 		the multiplication matrix
   * @return 		the double representing the dot product
   */
  const double dotMultiply(AlgVector b); 

  /**
   * Computes the scalar product of this vector with a scalar
   *
   * @param s 		the scalar
   */
  const void scalarMultiply(double s); 

  /**
   * Changes the length of a vector.
   *
   * @param len 	the new length of the vector
   */
  void changeLength(double len); 

  /**
   * Returns the norm of the vector
   *
   * @return 		the norm of the vector
   */
  double norm(); 

  /**
   * Norms this vector to length 1.0
   */
  const void normVector() {
   
    double len = this->norm();
    this->scalarMultiply(1 / len);
  }

  /** 
   * Converts a vector to a string
   *
   * @return 		the converted string
   */
  string toString(); 
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.10 $");
  }
};
