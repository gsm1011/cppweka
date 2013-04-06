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

#ifndef _WEKA_BINARYSPARSEINSTANCE_H_
#define _WEKA_BINARYSPARSEINSTANCE_H_

#include <string>
#include <iostream>

using namespace std; 

/**
 * Class for storing a binary-data-only instance as a sparse vector. A
 * sparse instance only requires storage for those attribute values
 * that are non-zero.  Since the objective is to reduce storage
 * requirements for datasets with large numbers of default values,
 * this also includes nominal attributes -- the first nominal value
 * (i.e. that which has index 0) will not require explicit storage, so
 * rearrange your nominal attribute value orderings if
 * necessary. Missing values are not supported, and will be treated as 
 * 1 (true).
 *
 * @version $Revision: 1.13 $
 */
class BinarySparseInstance : public SparseInstance {

  /**
   * Constructor that generates a sparse instance from the given
   * instance. Reference to the dataset is set to NULL.
   * (ie. the instance doesn't have access to information about the
   * attribute types)
   *
   * @param instance the instance from which the attribute values
   * and the weight are to be copied
   */
public:
    BinarySparseInstance(Instance instance);
  
  /**
   * Constructor that copies the info from the given instance. 
   * Reference to the dataset is set to NULL.
   * (ie. the instance doesn't have access to information about the
   * attribute types)
   *
   * @param instance the instance from which the attribute
   * info is to be copied 
   */
  inline BinarySparseInstance(SparseInstance instance) {
    
    m_AttValues = NULL;
    m_Indices = instance.m_Indices;
    m_Weight = instance.m_Weight;
    m_NumAttributes = instance.m_NumAttributes;
    m_Dataset = NULL;
  }

  /**
   * Constructor that generates a sparse instance from the given
   * parameters. Reference to the dataset is set to NULL.
   * (ie. the instance doesn't have access to information about the
   * attribute types)
   *
   * @param weight the instance's weight
   * @param attValues a vector of attribute values 
   */
    BinarySparseInstance(double weight, double[] attValues);
      
  /**
   * Constructor that inititalizes instance variable with given
   * values. Reference to the dataset is set to NULL. (ie. the instance
   * doesn't have access to information about the attribute types)
   *
   * @param weight the instance's weight
   * @param indices the indices of the given values in the full vector
   * @param maxNumValues the maximium number of values that can be stored
   */
  inline BinarySparseInstance(double weight,
                              int[] indices, int maxNumValues) {
    
    m_AttValues = NULL;
    m_Indices = indices;
    m_Weight = weight;
    m_NumAttributes = maxNumValues;
    m_Dataset = NULL;
  }

  /**
   * Constructor of an instance that sets weight to one, all values to
   * 1, and the reference to the dataset to NULL. (ie. the instance
   * doesn't have access to information about the attribute types)
   *
   * @param numAttributes the size of the instance 
   */
    BinarySparseInstance(int numAttributes);

  /**
   * Merges this instance with the given instance and returns
   * the result. Dataset is set to NULL.
   *
   * @param inst the instance to be merged with this one
   * @return the merged instances
   */
    Instance mergeInstance(Instance inst);

  /** 
   * Does nothing, since we don't support missing values.
   *
   * @param array containing the means and modes
   */
  inline void replaceMissingValues(double[] array) {
	 
    // Does nothing, since we don't store missing values.
  }

  /**
   * Sets a specific value in the instance to the given value 
   * (internal floating-point format). Performs a deep copy
   * of the vector of attribute values before the value is set.
   *
   * @param attIndex the attribute's index 
   * @param value the new attribute value (If the corresponding
   * attribute is nominal (or a string) then this is the new value's
   * index as a double).  
   */
    void setValue(int attIndex, double value);

  /**
   * Sets a specific value in the instance to the given value 
   * (internal floating-point format). Performs a deep copy
   * of the vector of attribute values before the value is set.
   *
   * @param indexOfIndex the index of the attribute's index 
   * @param value the new attribute value (If the corresponding
   * attribute is nominal (or a string) then this is the new value's
   * index as a double).  
   */
    void setValueSparse(int indexOfIndex, double value);

  /**
   * Returns the values of each attribute as an array of doubles.
   *
   * @return an array containing all the instance attribute values
   */
    double[] toDoubleArray();

  /**
   * Returns the description of one instance in sparse format. 
   * If the instance doesn't have access to a dataset, it returns the 
   * internal floating-point values. Quotes string values that contain 
   * whitespace characters.
   *
   * @return the instance's description as a string
   */
    string toString();

  /**
   * Returns an instance's attribute value in internal format.
   *
   * @param attIndex the attribute's index
   * @return the specified value as a double (If the corresponding
   * attribute is nominal (or a string) then it returns the value's index as a 
   * double).
   */
    double value(int attIndex);

  /**
   * Returns an instance's attribute value in internal format.
   * Does exactly the same thing as value() if applied to an Instance.
   *
   * @param indexOfIndex the index of the attribute's index
   * @return the specified value as a double (If the corresponding
   * attribute is nominal (or a string) then it returns the value's index as a 
   * double).
   */
  inline double valueSparse(int indexOfIndex) {

    int index = m_Indices[indexOfIndex]; // Throws if out of bounds
    return 1;
  }  

  /**
   * Deletes an attribute at the given position (0 to 
   * numAttributes() - 1).
   *
   * @param position the attribute's position
   */
    void forceDeleteAttributeAt(int position);

  /**
   * Inserts an attribute at the given position
   * (0 to numAttributes()) and sets its value to 1. 
   *
   * @param position the attribute's position
   */
    void forceInsertAttributeAt(int position);

  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  inline string getRevision() {
    return RevisionUtils.extract("$Revision: 1.13 $");
  }

    static void main(String[] options); 
};
  
#endif
