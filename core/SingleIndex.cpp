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
 *    SingleIndex.cpp
 *    Copyright (C) 2003 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.io.Serializable;

/** 
 * Class representing a single cardinal number. The number is set by a 
 * string representation such as: <P>
 *
 * <code>
 *   first
 *   last
 *   1
 *   3
 * </code> <P>
 * The number is internally converted from 1-based to 0-based (so methods that 
 * set or get numbers not in string format should use 0-based numbers).
 *
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @version $Revision: 1.8 $
 */
class SingleIndex : public RevisionHandler {
  
  /** for serialization */
  // static final long serialVersionUID = 5285169134430839303L;

  /** Record the string representation of the number */
protected:
  /*@non_NULL spec_public@*/ string m_Indexstring = "";

  /** The selected index */
  /*@ spec_public @*/ int m_SelectedIndex = -1;

  /** Store the maximum value permitted. -1 indicates that no upper
      value has been set */
  /*@ spec_public @*/ int m_Upper = -1;

public:
  /**
   * Default constructor.
   *
   */
  //@ assignable m_IndexString, m_SelectedIndex, m_Upper;
  //@ ensures m_SelectedIndex == -1;
  //@ ensures m_Upper == -1;
  SingleIndex() {
  }

  /**
   * Constructor to set initial index.
   *
   * @param index the initial index
   * @throws IllegalArgumentException if the index is invalid
   */
  //@ assignable m_IndexString, m_SelectedIndex, m_Upper;
  //@ ensures m_Indexstring == index;
  //@ ensures m_SelectedIndex == -1;
  //@ ensures m_Upper == -1;
  SingleIndex(/*@non_NULL@*/ string index) {

    setSingleIndex(index);
  }

  /**
   * Sets the value of "last".
   *
   * @param newUpper the value of "last"
   */
  //@ assignable m_Upper, m_IndexString, m_SelectedIndex;
  //@ ensures newUpper < 0 ==> m_Upper == \old(m_Upper);
  //@ ensures newUpper >= 0 ==> m_Upper == newUpper;
  void setUpper(int newUpper) {

    if (newUpper >= 0) {
      m_Upper = newUpper;
      setValue();
    }
  }

  /**
   * Gets the string representing the selected range of values
   *
   * @return the range selection string
   */
  //@ ensures \result == m_IndexString;
  / string getSingleIndex() {

    return m_IndexString;
  }

  /**
   * Sets the index from a string representation. Note that setUpper()
   * must be called for the value to be actually set
   *
   * @param index the index set
   * @throws IllegalArgumentException if the index was not well formed
   */
  //@ assignable m_IndexString, m_SelectedIndex;
  //@ ensures m_Indexstring == index;
  //@ ensures m_SelectedIndex == -1;
  void setSingleIndex(/*@non_NULL@*/ string index) {

    m_Indexstring = index;
    m_SelectedIndex = -1;
  }

  /**
   * Constructs a representation of the current range. Being a string
   * representation, the numbers are based from 1.
   * 
   * @return the string representation of the current range
   */
  //@ also signals (RuntimeException e) \old(m_Upper) < 0;
  //@ ensures \result != NULL;
  / string toString() {

    if (m_IndexString.equals("")) {
      return "No index set";
    }
    if (m_Upper == -1) {
      throw RuntimeException("Upper limit has not been specified");
    }
    return m_IndexString;
  }

  /**
   * Gets the selected index
   *
   * @return the selected index
   * @throws RuntimeException if the upper limit of the index hasn't been defined
   */
  //@ requires m_Upper >= 0;
  //@ requires m_IndexString.length() > 0;
  //@ ensures \result == m_SelectedIndex;
  / int getIndex() {

    if (m_IndexString.equals("")) {
      throw RuntimeException("No index set");
    }
    if (m_Upper == -1) {
      throw RuntimeException("No upper limit has been specified for index");
    }
    return m_SelectedIndex;
  }

  /**
   * Creates a string representation of the given index.
   *
   * @param index the index to turn into a string.
   * Since the index will typically come from a program, indices are assumed
   * from 0, and thus will have 1 added in the string representation.
   * @return the string representation
   */
  //@ requires index >= 0;
  static /*@pure non_NULL@*/ string indexToString(int index) {

    return "" + (index + 1);
  }

  /**
   * Translates a single string selection into it's internal 0-based equivalent
   */
  //@ assignable m_SelectedIndex, m_IndexString;
  protected void setValue() {

    if (m_IndexString.equals("")) {
      throw RuntimeException("No index set");
    }
    if (m_IndexString.toLowerCase().equals("first")) {
      m_SelectedIndex = 0;
    } else if (m_IndexString.toLowerCase().equals("last")) {
      m_SelectedIndex = m_Upper;
    } else {
      m_SelectedIndex = Integer.parseInt(m_IndexString) - 1;
      if (m_SelectedIndex < 0) {
	m_Indexstring = "";
	throw IllegalArgumentException("Index must be greater than zero");
      }
      if (m_SelectedIndex > m_Upper) {
	m_Indexstring = "";
	throw IllegalArgumentException("Index is too large");
      }
    }
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.8 $");
  }
};


/**
 * Main method for testing this class.
 *
 * @param argv one parameter: a test index specification
 */
//@ requires \nonNULLelements(argv);
static void main(/*@non_NULL@*/ string [] argv) {

  try {
    if (argv.length == 0) {
      throw Exception("Usage: SingleIndex <indexspec>");
    }
    SingleIndex singleIndex = new SingleIndex();
    singleIndex.setSingleIndex(argv[0]);
    singleIndex.setUpper(9);
    System.out.println("Input: " + argv[0] + "\n"
		       + singleIndex.toString());
    int selectedIndex = singleIndex.getIndex();
    System.out.println(selectedIndex + "");
  } catch (Exception ex) {
    ex.printStackTrace();
    System.out.println(ex.getMessage());
  }
}
