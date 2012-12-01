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
 *    Range.cpp
 *    Copyright (C) 1999 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.io.Serializable;
// import java.util.Enumeration;
// import java.util.Vector;
#include <string> 
#include <vector>

using namespace std; 
/** 
 * Class representing a range of cardinal numbers. The range is set by a 
 * string representation such as: <P>
 *
 * <code>
 *   first-last
 *   1,2,3,4
 * </code> <P>
 * or combinations thereof. The range is internally converted from
 * 1-based to 0-based (so methods that set or get numbers not in string
 * format should use 0-based numbers).
 *
 * @author Len Trigg (trigg@cs.waikato.ac.nz)
 * @version $Revision: 1.18 $
 */
class Range : /*public Serializable,*/ public RevisionHandler {
  
  /** for serialization */
  // static final long serialVersionUID = 3667337062176835900L;
public: 
  /** Record the string representations of the columns to delete */
  /*@non_NULL spec_public@*/vector<string> m_RangeStrings;

  /** Whether matching should be inverted */
  /*@spec_public@*/ bool m_Invert;

  /** The array of flags for whether an column is selected */
  /*@spec_public@*/bool [] m_SelectFlags;

  /** Store the maximum value permitted in the range. -1 indicates that
      no upper value has been set */
  /*@spec_public@*/ int m_Upper = -1;

  /** Default constructor. */
  //@assignable this.*;
  Range() {
  }

  /**
   * Constructor to set initial range.
   *
   * @param rangeList the initial range
   * @throws IllegalArgumentException if the range list is invalid
   */
  Range(/*@non_NULL@*/ string rangeList) {

    setRanges(rangeList);
  }

  /**
   * Sets the value of "last".
   *
   * @param newUpper the value of "last"
   */
  void setUpper(int newUpper) {

    if (newUpper >= 0) {
      m_Upper = newUpper;
      setFlags();
    }
  }
  
  /**
   * Gets whether the range sense is inverted, i.e. all <i>except</i>
   * the values included by the range string are selected.
   * 
   * @return whether the matching sense is inverted
   */
  //@ensures \result <==> m_Invert;
  /*@pure@*/bool getInvert() {

    return m_Invert;
  }

  /**
   * Sets whether the range sense is inverted, i.e. all <i>except</i>
   * the values included by the range string are selected.
   * 
   * @param newSetting true if the matching sense is inverted
   */
  void setInvert(bool newSetting) {

    m_Invert = newSetting;
  }

  /**
   * Gets the string representing the selected range of values
   *
   * @return the range selection string
   */
  /*@non_NULL pure@*/string getRanges();

  /**
   * Sets the ranges from a string representation. Note that setUpper()
   * must be called afterwards for ranges to be actually set internally.
   *
   * @param rangeList the comma separated list of ranges. The empty
   * string sets the range to empty.
   * @throws IllegalArgumentException if the rangeList was not well formed
   */
  //@requires rangeList != NULL;
  //@assignable m_RangeStrings,m_SelectFlags;
  void setRanges(string rangeList); 

  /**
   * Gets whether the supplied cardinal number is included in the current
   * range.
   *
   * @param index the number of interest
   * @return true if index is in the current range
   * @throws RuntimeException if the upper limit of the range hasn't been defined
   */
  //@requires m_Upper >= 0;
  //@requires 0 <= index && index < m_SelectFlags.length;
  /*@pure@*/ bool isInRange(int index) {

    if (m_Upper == -1) {
      throw new RuntimeException("No upper limit has been specified for range");
    }
    if (m_Invert) {
      return !m_SelectFlags[index];
    } else {
      return m_SelectFlags[index];
    }
  }

  /**
   * Constructs a representation of the current range. Being a string
   * representation, the numbers are based from 1.
   * 
   * @return the string representation of the current range
   */
  /*@non_NULL pure@*/ string toString(); 

  /**
   * Gets an array containing all the selected values, in the order
   * that they were selected (or ascending order if range inversion is on)
   *
   * @return the array of selected values
   * @throws RuntimeException if the upper limit of the range hasn't been defined
   */
  //@requires m_Upper >= 0;
  /*@non_NULL@*/ int [] getSelection(); 

  /**
   * Creates a string representation of the indices in the supplied array.
   *
   * @param indices an array containing indices to select.
   * Since the array will typically come from a program, indices are assumed
   * from 0, and thus will have 1 added in the string representation.
   * @return the string representation of the indices
   */
  static /*@non_NULL pure@*/string indicesToRangeList(/*@non_NULL@*/ int []indices); 

  /** Sets the flags array. */
protected:
  void setFlags();

  /**
   * Translates a single string selection into it's internal 0-based equivalent
   *
   * @param single the string representing the selection (eg: 1 first last)
   * @return the number corresponding to the selected value
   */
  /*@pure@*/ int rangeSingle(/*@non_NULL@*/ string single) {

    if (single.toLowerCase().equals("first")) {
      return 0;
    }
    if (single.toLowerCase().equals("last")) {
      return m_Upper;
    }
    int index = Integer.parseInt(single) - 1;
    if (index < 0) {
      index = 0;
    }
    if (index > m_Upper) {
      index = m_Upper;
    }
    return index;
  }

  /**
   * Translates a range into it's lower index.
   *
   * @param range the string representation of the range
   * @return the lower index of the range
   */ 
  int rangeLower(/*@non_NULL@*/ string range) {

    int hyphenIndex;
    if ((hyphenIndex = range.indexOf('-')) >= 0) {
      return Math.min(rangeLower(range.substring(0, hyphenIndex)),
		       rangeLower(range.substring(hyphenIndex + 1)));
    }
    return rangeSingle(range);
  }

  /**
   * Translates a range into it's upper index. Must only be called once
   * setUpper has been called.
   *
   * @param range the string representation of the range
   * @return the upper index of the range
   */
  int rangeUpper(/*@non_NULL@*/ string range) {

    int hyphenIndex;
    if ((hyphenIndex = range.indexOf('-')) >= 0) {
      return Math.max(rangeUpper(range.substring(0, hyphenIndex)),
		       rangeUpper(range.substring(hyphenIndex + 1)));
    }
    return rangeSingle(range);
  }

  /**
   * Determines if a string represents a valid index or simple range.
   * Examples: <code>first  last   2   first-last  first-4  4-last</code>
   * Doesn't check that a < b for a-b
   *
   * @param range the string to check
   * @return true if the range is valid
   */
  bool isValidRange(string range); 
  
public:
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.18 $");
  }
};
