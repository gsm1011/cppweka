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
 * StringLocator.cpp
 * Copyright (C) 2005 University of Waikato, Hamilton, New Zealand
 */

// package weka.core;
#include <iostream>
#include <vector>
#include <string>

using namespace std;
/**
 * This class locates and records the indices of a certain type of attributes,
 * recursively in case of Relational attributes.
 *
 * @author fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.4 $
 * @see Attribute#RELATIONAL
 */
class AttributeLocator : public Comparable<AttributeLocator>,
			 public RevisionHandler {

  /** for serialization */
  // // // // // private static final long serialVersionUID = -2932848827681070345L;
protected:
  /** the attribute indices that may be inspected */
  int[] m_AllowedIndices = NULL;

  /** contains the attribute locations, either true or false Boolean objects */
  Vector m_Attributes = NULL;

  /** contains the locator locations, either NULL or a AttributeLocator reference */
  Vector m_Locators = NULL;

  /** the type of the attribute */
  int m_Type = -1;

  /** the referenced data */
  Instances m_Data = NULL;

  /** the indices */
  int[] m_Indices = NULL;

  /** the indices of locator objects */
  int[] m_LocatorIndices = NULL;

  /**
   * Initializes the AttributeLocator with the given data for the specified
   * type of attribute. Checks all attributes.
   *
   * @param data	the data to work on
   * @param type	the type of attribute to locate
   */
public:
  AttributeLocator(Instances data, int type) {
    this(data, type, 0, data.numAttributes() - 1);
  }

  /**
   * Initializes the AttributeLocator with the given data for the specified
   * type of attribute. Checks only the given range.
   *
   * @param data	the data to work on
   * @param type	the type of attribute to locate
   * @param fromIndex	the first index to inspect (including)
   * @param toIndex	the last index to check (including)
   */
  AttributeLocator(Instances data, int type, int fromIndex, int toIndex) {
    super();

    int[] indices = new int[toIndex - fromIndex + 1];
    for (int i = 0; i < indices.length; i++)
      indices[i] = fromIndex + i;

    initialize(data, type, indices);
  }

  /**
   * initializes the AttributeLocator with the given data for the specified
   * type of attribute. Checks only the given attribute indices.
   *
   * @param data	the data to work on
   * @param type	the type of attribute to locate
   * @param indices	the attribute indices to check
   */
  AttributeLocator(Instances data, int type, int[] indices) {
    super();

    initialize(data, type, indices);
  }

  /**
   * returns the type of attribute that is located
   *
   * @return		the type of attribute
   */
  int getType() {
    return m_Type;
  }

  /**
   * returns the indices that are allowed to check for the attribute type
   *
   * @return 		the indices that are checked for the attribute type
   */
  int[] getAllowedIndices() {
    return m_AllowedIndices;
  }

protected:
  /**
   * initializes the AttributeLocator
   *
   * @param data	the data to base the search for attributes on
   * @param type	the type of attribute to look for
   * @param indices	the indices that are allowed to check
   */
  void initialize(Instances data, int type, int[] indices) {
    m_Data = new Instances(data, 0);
    m_Type = type;

    m_AllowedIndices = new int[indices.length];
    System.arraycopy(indices, 0, m_AllowedIndices, 0, indices.length);

    locate();

    m_Indices        = find(true);
    m_LocatorIndices = find(false);
  }

  /**
   * sets up the structure
   */
  void locate() {
    int         i;

    m_Attributes = new Vector();
    m_Locators   = new Vector();

    for (i = 0; i < m_AllowedIndices.length; i++) {
      if (m_Data.attribute(m_AllowedIndices[i]).type() == Attribute.RELATIONAL)
	m_Locators.add(new AttributeLocator(m_Data.attribute(m_AllowedIndices[i]).relation(), getType()));
      else
	m_Locators.add(NULL);

      if (m_Data.attribute(m_AllowedIndices[i]).type() == getType())
        m_Attributes.add(new Boolean(true));
      else
        m_Attributes.add(new Boolean(false));
    }
  }

  /**
   * returns the indices of the searched-for attributes (if TRUE) or the indices
   * of AttributeLocator objects (if FALSE)
   *
   * @param findAtts      if true the indices of attributes are located,
   *                      otherwise the ones of AttributeLocator objects
   * @return              the indices of the attributes or the AttributeLocator objects
   */

  int[] find(bool findAtts) {
    int		i;
    int[]	result;
    Vector	indices;

    // determine locations
    indices = new Vector();
    if (findAtts) {
      for (i = 0; i < m_Attributes.size(); i++) {
	if (((Boolean) m_Attributes.get(i)).boolValue())
	  indices.add(new Integer(i));
      }
    }
    else {
      for (i = 0; i < m_Locators.size(); i++) {
	if (m_Locators.get(i) != NULL)
	  indices.add(new Integer(i));
      }
    }

    // fill array
    result = new int[indices.size()];
    for (i = 0; i < indices.size(); i++)
      result[i] = ((Integer) indices.get(i)).intValue();

    return result;
  }

public:
  /**
   * returns actual index in the Instances object.
   *
   * @param index	the index in the m_AllowedIndices array
   * @return		the actual index in the instances object
   */
  int getActualIndex(int index) {
    return m_AllowedIndices[index];
  }


  /**
   * returns the underlying data
   *
   * @return      the underlying Instances object
   */
  Instances getData() {
    return m_Data;
  }

  /**
   * Returns the indices of the attributes. These indices are referring
   * to the m_AllowedIndices array, not the actual indices in the Instances
   * object.
   *
   * @return	the indices of the attributes
   * @see	#getActualIndex(int)
   */
  int[] getAttributeIndices() {
    return m_Indices;
  }

  /**
   * Returns the indices of the AttributeLocator objects.  These indices are
   * referring to the m_AllowedIndices array, not the actual indices in the
   * Instances object.
   *
   * @return	the indices of the AttributeLocator objects
   * @see	#getActualIndex(int)
   */
  int[] getLocatorIndices() {
    return m_LocatorIndices;
  }

  /**
   * Returns the AttributeLocator at the given index. This index refers to
   * the index of the m_AllowedIndices array, not the actual Instances object.
   *
   * @param index   the index of the locator to retrieve
   * @return        the AttributeLocator at the given index
   */
  AttributeLocator getLocator(int index) {
    return (AttributeLocator) m_Locators.get(index);
  }

  /**
   * Compares this object with the specified object for order. Returns a
   * negative integer, zero, or a positive integer as this object is less
   * than, equal to, or greater than the specified object. Only type and
   * indices are checked.
   *
   * @param o		the object to compare with
   * @return		-1 if less than, 0 if equal, +1 if greater than the
   * 			given object
   */
  int compareTo(AttributeLocator o) {
    int		result;
    int		i;

    result = 0;

    // 1. check type
    if (this->getType() < o.getType()) {
      result = -1;
    }
    else if (this->getType() > o.getType()) {
      result = 1;
    }
    else {
      // 2. check indices
      if (this->getAllowedIndices().length < o.getAllowedIndices().length) {
	result = -1;
      }
      else if (this->getAllowedIndices().length > o.getAllowedIndices().length) {
	result = 1;
      }
      else {
	for (i = 0; i < this->getAllowedIndices().length; i++) {
	  if (this->getAllowedIndices()[i] < o.getAllowedIndices()[i]) {
	    result = -1;
	    break;
	  }
	  else if (this->getAllowedIndices()[i] > o.getAllowedIndices()[i]) {
	    result = 1;
	    break;
	  }
	  else {
	    result = 0;
	  }
	}
      }
    }

    return result;
  }

  /**
   * Indicates whether some other object is "equal to" this one. Only type
   * and indices are checked.
   *
   * @param o		the AttributeLocator to check for equality
   * @return		true if the AttributeLocators have the same type and
   * 			indices
   */
  bool equals(Object o) {
    return (compareTo((AttributeLocator) o) == 0);
  }

  /**
   * returns a string representation of this object
   *
   * @return 		a string representation
   */
  string toString() {
    return m_Attributes.toString();
  }

  /**
   * Returns the revision string.
   *
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.4 $");
  }
};
