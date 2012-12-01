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
 *    Attribute.cpp
 *    Copyright (C) 1999 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.io.IOException;
// import java.io.Serializable;
// import java.io.StreamTokenizer;
// import java.io.StringReader;
// import java.text.ParseException;
// import java.text.SimpleDateFormat;
// import java.util.Date;
// import java.util.Enumeration;
// import java.util.Hashtable;
// import java.util.Properties;
#include <string>
#include <stringstream>
#include "Copyable"
#include "Serializable"
#include "RevisionHandler"

using namespace std; 

/** 
 * Class for handling an attribute. Once an attribute has been created,
 * it can't be changed. <p>
 *
 * The following attribute types are supported:
 * <ul>
 *    <li> numeric: <br/>
 *         This type of attribute represents a floating-point number.
 *    </li>
 *    <li> nominal: <br/>
 *         This type of attribute represents a fixed set of nominal values.
 *    </li>
 *    <li> string: <br/>
 *         This type of attribute represents a dynamically expanding set of
 *         nominal values. Usually used in text classification.
 *    </li>
 *    <li> date: <br/>
 *         This type of attribute represents a date, internally represented as 
 *         floating-point number storing the milliseconds since January 1, 
 *         1970, 00:00:00 GMT. The string representation of the date must be
 *         <a href="http://www.iso.org/iso/en/prods-services/popstds/datesandtime.html" target="_blank">
 *         ISO-8601</a> compliant, the default is <code>yyyy-MM-dd'T'HH:mm:ss</code>.
 *    </li>
 *    <li> relational: <br/>
 *         This type of attribute can contain other attributes and is, e.g., 
 *         used for representing Multi-Instance data. (Multi-Instance data
 *         consists of a nominal attribute containing the bag-id, then a 
 *         relational attribute with all the attributes of the bag, and 
 *         finally the class attribute.)
 *    </li>
 * </ul>
 * 
 * Typical usage (code from the main() method of this class): <p>
 *
 * <code>
 * ... <br>
 *
 * // Create numeric attributes "length" and "weight" <br>
 * Attribute length = new Attribute("length"); <br>
 * Attribute weight = new Attribute("weight"); <br><br>
 * 
 * // Create vector to hold nominal values "first", "second", "third" <br>
 * FastVector my_nominal_values = new FastVector(3); <br>
 * my_nominal_values.addElement("first"); <br>
 * my_nominal_values.addElement("second"); <br>
 * my_nominal_values.addElement("third"); <br><br>
 *
 * // Create nominal attribute "position" <br>
 * Attribute position = new Attribute("position", my_nominal_values);<br>
 *
 * ... <br>
 * </code><p>
 *
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @version $Revision: 5975 $
 */
class Attribute : public Copyable, 
		  public Serializable, public RevisionHandler {

  /** for serialization */
  // static final long serialVersionUID = -742180568732916383L;
public:
  /** Constant set for numeric attributes. */
  const static int NUMERIC = 0;

  /** Constant set for nominal attributes. */
  const static int NOMINAL = 1;

  /** Constant set for attributes with string values. */
  const static int STRING = 2;

  /** Constant set for attributes with date values. */
  const static int DATE = 3;

  /** Constant set for relation-valued attributes. */
  const static int RELATIONAL = 4;

  /** Constant set for symbolic attributes. */
  const static int ORDERING_SYMBOLIC = 0;

  /** Constant set for ordered attributes. */
  const static int ORDERING_ORDERED  = 1;

  /** Constant set for modulo-ordered attributes. */
  const static int ORDERING_MODULO   = 2;

  /** The keyword used to denote the start of an arff attribute declaration */
  const static string ARFF_ATTRIBUTE = "@attribute";

  /** A keyword used to denote a numeric attribute */
  const static string ARFF_ATTRIBUTE_INTEGER = "integer";

  /** A keyword used to denote a numeric attribute */
  const static string ARFF_ATTRIBUTE_REAL = "real";

  /** A keyword used to denote a numeric attribute */
  const static string ARFF_ATTRIBUTE_NUMERIC = "numeric";

  /** The keyword used to denote a string attribute */
  const static string ARFF_ATTRIBUTE_STRING = "string";

  /** The keyword used to denote a date attribute */
  const static string ARFF_ATTRIBUTE_DATE = "date";

  /** The keyword used to denote a relation-valued attribute */
  const static string ARFF_ATTRIBUTE_RELATIONAL = "relational";

  /** The keyword used to denote the end of the declaration of a subrelation */
  const static string ARFF_END_SUBRELATION = "@end";

private:
  /** Strings longer than this will be stored compressed. */
  const static int STRING_COMPRESS_THRESHOLD = 200;

  /** The attribute's name. */
  /*@ spec_public non_NULL @*/ string m_Name;

  /** The attribute's type. */
  /*@ spec_public @*/ int m_Type;
  /*@ invariant m_Type == NUMERIC || 
                m_Type == DATE || 
                m_Type == STRING || 
                m_Type == NOMINAL ||
                m_Type == RELATIONAL;
  */

  /** The attribute's values (if nominal or string). */
  /*@ spec_public @*/ FastVector m_Values;

  /** Mapping of values to indices (if nominal or string). */
  Hashtable m_Hashtable;

  /** The header information for a relation-valued attribute. */
  Instances m_Header;

  /** Date format specification for date attributes */
  SimpleDateFormat m_DateFormat;

  /** The attribute's index. */
  /*@ spec_public @*/ int m_Index;

  /** The attribute's metadata. */
  ProtectedProperties m_Metadata;

  /** The attribute's ordering. */
  int m_Ordering;

  /** Whether the attribute is regular. */
  bool m_IsRegular;

  /** Whether the attribute is averagable. */
  bool m_IsAveragable;

  /** Whether the attribute has a zeropoint. */
  bool m_HasZeropoint;

  /** The attribute's weight. */
  double m_Weight;

  /** The attribute's lower numeric bound. */
  double m_LowerBound;

  /** Whether the lower bound is open. */
  bool m_LowerBoundIsOpen;

  /** The attribute's upper numeric bound. */
  double m_UpperBound;

  /** Whether the upper bound is open */
  bool m_UpperBoundIsOpen;

public:
  /**
   * Constructor for a numeric attribute.
   *
   * @param attributeName the name for the attribute
   */
  //@ requires attributeName != NULL;
  //@ ensures  m_Name == attributeName;
  Attribute(string attributeName) {

    this(attributeName, new ProtectedProperties(new Properties()));
  }

  /**
   * Constructor for a numeric attribute, where metadata is supplied.
   *
   * @param attributeName the name for the attribute
   * @param metadata the attribute's properties
   */
  //@ requires attributeName != NULL;
  //@ requires metadata != NULL;
  //@ ensures  m_Name == attributeName;
  Attribute(string attributeName, ProtectedProperties metadata) {

    m_Name = attributeName;
    m_Index = -1;
    m_Values = NULL;
    m_Hashtable = NULL;
    m_Header = NULL;
    m_Type = NUMERIC;
    setMetadata(metadata);
  }

  /**
   * Constructor for a date attribute.
   *
   * @param attributeName the name for the attribute
   * @param dateFormat a string suitable for use with
   * SimpleDateFormatter for parsing dates.
   */
  //@ requires attributeName != NULL;
  //@ requires dateFormat != NULL;
  //@ ensures  m_Name == attributeName;
  Attribute(string attributeName, string dateFormat) {

    this(attributeName, dateFormat,
	 new ProtectedProperties(new Properties()));
  }

  /**
   * Constructor for a date attribute, where metadata is supplied.
   *
   * @param attributeName the name for the attribute
   * @param dateFormat a string suitable for use with
   * SimpleDateFormatter for parsing dates.
   * @param metadata the attribute's properties
   */
  //@ requires attributeName != NULL;
  //@ requires dateFormat != NULL;
  //@ requires metadata != NULL;
  //@ ensures  m_Name == attributeName;
  Attribute(string attributeName, string dateFormat,
		   ProtectedProperties metadata) {

    m_Name = attributeName;
    m_Index = -1;
    m_Values = NULL;
    m_Hashtable = NULL;
    m_Header = NULL;
    m_Type = DATE;
    if (dateFormat != NULL) {
      m_DateFormat = new SimpleDateFormat(dateFormat);
    } else {
      m_DateFormat = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss");
    }
    m_DateFormat.setLenient(false);
    setMetadata(metadata);
  }

  /**
   * Constructor for nominal attributes and string attributes.
   * If a NULL vector of attribute values is passed to the method,
   * the attribute is assumed to be a string.
   *
   * @param attributeName the name for the attribute
   * @param attributeValues a vector of strings denoting the 
   * attribute values. Null if the attribute is a string attribute.
   */
  //@ requires attributeName != NULL;
  //@ ensures  m_Name == attributeName;
  Attribute(string attributeName, 
		   FastVector attributeValues) {

    this(attributeName, attributeValues,
	 new ProtectedProperties(new Properties()));
  }

  /**
   * Constructor for nominal attributes and string attributes, where
   * metadata is supplied. If a NULL vector of attribute values is passed
   * to the method, the attribute is assumed to be a string.
   *
   * @param attributeName the name for the attribute
   * @param attributeValues a vector of strings denoting the 
   * attribute values. Null if the attribute is a string attribute.
   * @param metadata the attribute's properties
   */
  //@ requires attributeName != NULL;
  //@ requires metadata != NULL;
  /*@ ensures  m_Name == attributeName;
      ensures  m_Index == -1;
      ensures  attributeValues == NULL && m_Type == STRING
            || attributeValues != NULL && m_Type == NOMINAL 
                  && m_Values.size() == attributeValues.size();
      signals (IllegalArgumentException ex) 
                 (* if duplicate strings in attributeValues *);
  */
  Attribute(string attributeName, 
	    FastVector attributeValues,
	    ProtectedProperties metadata); 

  /**
   * Constructor for relation-valued attributes.
   *
   * @param attributeName the name for the attribute
   * @param header an Instances object specifying the header of the relation.
   */
  Attribute(string attributeName, Instances header) {

    this(attributeName, header,
	 new ProtectedProperties(new Properties()));
  }

  /**
   * Constructor for relation-valued attributes.
   *
   * @param attributeName the name for the attribute
   * @param header an Instances object specifying the header of the relation.
   * @param metadata the attribute's properties
   */
  Attribute(string attributeName, 
		   Instances header,
		   ProtectedProperties metadata) {

    if (header.numInstances() > 0) {
      throw new IllegalArgumentException("Header for relation-valued " +
                                         "attribute should not contain " +
                                         "any instances");
    }
    m_Name = attributeName;
    m_Index = -1;
    m_Values = new FastVector();
    m_Hashtable = new Hashtable();
    m_Header = header;
    m_Type = RELATIONAL;
    setMetadata(metadata);
  }

  /**
   * Produces a shallow copy of this attribute.
   *
   * @return a copy of this attribute with the same index
   */
  //@ also ensures \result instanceof Attribute;
  /*@ pure non_NULL @*/ Object copy() {

    Attribute copy = new Attribute(m_Name);

    copy.m_Index = m_Index;
    copy.m_Type = m_Type;
    copy.m_Values = m_Values;
    copy.m_Hashtable = m_Hashtable;
    copy.m_DateFormat = m_DateFormat;
    copy.m_Header = m_Header;
    copy.setMetadata(m_Metadata);
 
    return copy;
  }

  /**
   * Returns an enumeration of all the attribute's values if the
   * attribute is nominal, string, or relation-valued, NULL otherwise.
   *
   * @return enumeration of all the attribute's values
   */
  /*@ pure @*/ Enumeration enumerateValues() {

    if (isNominal() || isString()) {
      const Enumeration ee = m_Values.elements();
      return new Enumeration () {
          bool hasMoreElements() {
            return ee.hasMoreElements();
          }
          Object nextElement() {
            Object oo = ee.nextElement();
            if (oo instanceof SerializedObject) {
              return ((SerializedObject)oo).getObject();
            } else {
              return oo;
            }
          }
        };
    }
    return NULL;
  }

  /**
   * Tests if given attribute is equal to this attribute.
   *
   * @param other the Object to be compared to this attribute
   * @return true if the given attribute is equal to this attribute
   */
  /*@ pure @*/ bool equals(Object other); 

  /**
   * Returns the index of this attribute.
   *
   * @return the index of this attribute
   */
  //@ ensures \result == m_Index;
  /*@ pure @*/ int index() {

    return m_Index;
  }

  /**
   * Returns the index of a given attribute value. (The index of
   * the first occurence of this value.)
   *
   * @param value the value for which the index is to be returned
   * @return the index of the given attribute value if attribute
   * is nominal or a string, -1 if it is not or the value 
   * can't be found
   */
  int indexOfValue(string value) {

    if (!isNominal() && !isString())
      return -1;
    Object store = value;
    if (value.length() > STRING_COMPRESS_THRESHOLD) {
      try {
        store = new SerializedObject(value, true);
      } catch (Exception ex) {
        cout << "Couldn't compress string attribute value -"
	     << " searching uncompressed." << endl;
      }
    }
    Integer val = (Integer)m_Hashtable.get(store);
    if (val == NULL) return -1;
    else return val.intValue();
  }

  /**
   * Test if the attribute is nominal.
   *
   * @return true if the attribute is nominal
   */
  //@ ensures \result <==> (m_Type == NOMINAL);
  /*@ pure @*/ bool isNominal() {

    return (m_Type == NOMINAL);
  }

  /**
   * Tests if the attribute is numeric.
   *
   * @return true if the attribute is numeric
   */
  //@ ensures \result <==> ((m_Type == NUMERIC) || (m_Type == DATE));
  /*@ pure @*/ bool isNumeric() {

    return ((m_Type == NUMERIC) || (m_Type == DATE));
  }

  /**
   * Tests if the attribute is relation valued.
   *
   * @return true if the attribute is relation valued
   */
  //@ ensures \result <==> (m_Type == RELATIONAL);
  /*@ pure @*/ bool isRelationValued() {

    return (m_Type == RELATIONAL);
  }

  /**
   * Tests if the attribute is a string.
   *
   * @return true if the attribute is a string
   */
  //@ ensures \result <==> (m_Type == STRING);
  /*@ pure @*/ bool isString() {

    return (m_Type == STRING);
  }

  /**
   * Tests if the attribute is a date type.
   *
   * @return true if the attribute is a date type
   */
  //@ ensures \result <==> (m_Type == DATE);
  /*@ pure @*/ bool isDate() {

    return (m_Type == DATE);
  }

  /**
   * Returns the attribute's name.
   *
   * @return the attribute's name as a string
   */
  //@ ensures \result == m_Name;
  /*@ pure @*/ string name() {

    return m_Name;
  }
  
  /**
   * Returns the number of attribute values. Returns 0 for 
   * attributes that are not either nominal, string, or
   * relation-valued.
   *
   * @return the number of attribute values
   */
  /*@ pure @*/ int numValues() {

    if (!isNominal() && !isString() && !isRelationValued()) {
      return 0;
    } else {
      return m_Values.size();
    }
  }

  /**
   * Returns a description of this attribute in ARFF format. Quotes
   * strings if they contain whitespace characters, or if they
   * are a question mark.
   *
   * @return a description of this attribute as a string
   */
  string toString(); 

  /**
   * Returns the attribute's type as an integer.
   *
   * @return the attribute's type.
   */
  //@ ensures \result == m_Type;
  /*@ pure @*/ int type() {

    return m_Type;
  }
  
  /**
   * Returns the Date format pattern in case this attribute is of type DATE,
   * otherwise an empty string.
   * 
   * @return the date format pattern
   * @see SimpleDateFormat
   */
  string getDateFormat() {
    if (isDate())
      return m_DateFormat.toPattern();
    else
      return "";
  }

  /**
   * Returns a value of a nominal or string attribute.  Returns an
   * empty string if the attribute is neither a string nor a nominal
   * attribute.
   *
   * @param valIndex the value's index
   * @return the attribute's value as a string
   */
  /*@ non_NULL pure @*/ string value(int valIndex) {
    
    if (!isNominal() && !isString()) {
      return "";
    } else {
      Object val = m_Values.elementAt(valIndex);
      
      // If we're storing strings compressed, uncompress it.
      if (val instanceof SerializedObject) {
        val = ((SerializedObject)val).getObject();
      }
      return (String) val;
    }
  }

  /**
   * Returns the header info for a relation-valued attribute,
   * NULL if the attribute is not relation-valued.
   *
   * @return the attribute's value as an Instances object
   */
  /*@ non_NULL pure @*/ Instances relation() {
    
    if (!isRelationValued()) {
      return NULL;
    } else {
      return m_Header;
    }
  }

  /**
   * Returns a value of a relation-valued attribute. Returns
   * NULL if the attribute is not relation-valued.
   *
   * @param valIndex the value's index
   * @return the attribute's value as an Instances object
   */
  /*@ non_NULL pure @*/ Instances relation(int valIndex) {
    
    if (!isRelationValued()) {
      return NULL;
    } else {
      return (Instances) m_Values.elementAt(valIndex);
    }
  }

  /**
   * Constructor for a numeric attribute with a particular index.
   *
   * @param attributeName the name for the attribute
   * @param index the attribute's index
   */
  //@ requires attributeName != NULL;
  //@ requires index >= 0;
  //@ ensures  m_Name == attributeName;
  //@ ensures  m_Index == index;
  Attribute(string attributeName, int index) {

    this(attributeName);
    m_Index = index;
  }

  /**
   * Constructor for date attributes with a particular index.
   *
   * @param attributeName the name for the attribute
   * @param dateFormat a string suitable for use with
   * SimpleDateFormatter for parsing dates.  Null for a default format
   * string.
   * @param index the attribute's index
   */
  //@ requires attributeName != NULL;
  //@ requires index >= 0;
  //@ ensures  m_Name == attributeName;
  //@ ensures  m_Index == index;
  Attribute(string attributeName, string dateFormat, 
	    int index) {

    this(attributeName, dateFormat);
    m_Index = index;
  }

  /**
   * Constructor for nominal attributes and string attributes with
   * a particular index.
   * If a NULL vector of attribute values is passed to the method,
   * the attribute is assumed to be a string.
   *
   * @param attributeName the name for the attribute
   * @param attributeValues a vector of strings denoting the attribute values.
   * Null if the attribute is a string attribute.
   * @param index the attribute's index
   */
  //@ requires attributeName != NULL;
  //@ requires index >= 0;
  //@ ensures  m_Name == attributeName;
  //@ ensures  m_Index == index;
  Attribute(string attributeName, FastVector attributeValues, 
	    int index) {

    this(attributeName, attributeValues);
    m_Index = index;
  }

  /**
   * Constructor for a relation-valued attribute with a particular index.
   *
   * @param attributeName the name for the attribute
   * @param header the header information for this attribute
   * @param index the attribute's index
   */
  //@ requires attributeName != NULL;
  //@ requires index >= 0;
  //@ ensures  m_Name == attributeName;
  //@ ensures  m_Index == index;
  Attribute(string attributeName, Instances header,
	    int index) {

    this(attributeName, header);
    m_Index = index;
  }

  /**
   * Adds a string value to the list of valid strings for attributes
   * of type STRING and returns the index of the string.
   *
   * @param value The string value to add
   * @return the index assigned to the string, or -1 if the attribute is not
   * of type Attribute.STRING 
   */
  /*@ requires value != NULL;
      ensures  isString() && 0 <= \result && \result < m_Values.size() ||
             ! isString() && \result == -1;
  */
  int addStringValue(string value) {

    if (!isString()) {
      return -1;
    }
    Object store = value;

    if (value.length() > STRING_COMPRESS_THRESHOLD) {
      try {
        store = new SerializedObject(value, true);
      } catch (Exception ex) {
        cout << "Couldn't compress string attribute value -"
	     << " storing uncompressed." << endl;
      }
    }
    Integer index = (Integer)m_Hashtable.get(store);
    if (index != NULL) {
      return index.intValue();
    } else {
      int intIndex = m_Values.size();
      m_Values.addElement(store);
      m_Hashtable.put(store, new Integer(intIndex));
      return intIndex;
    }
  }

  /**
   * Adds a string value to the list of valid strings for attributes
   * of type STRING and returns the index of the string. This method is
   * more efficient than addStringValue(String) for long strings.
   *
   * @param src The Attribute containing the string value to add.
   * @param index the index of the string value in the source attribute.
   * @return the index assigned to the string, or -1 if the attribute is not
   * of type Attribute.STRING 
   */
  /*@ requires src != NULL;
      requires 0 <= index && index < src.m_Values.size();
      ensures  isString() && 0 <= \result && \result < m_Values.size() ||
             ! isString() && \result == -1;
  */
  int addStringValue(Attribute src, int index) {

    if (!isString()) {
      return -1;
    }
    Object store = src.m_Values.elementAt(index);
    Integer oldIndex = (Integer)m_Hashtable.get(store);
    if (oldIndex != NULL) {
      return oldIndex.intValue();
    } else {
      int intIndex = m_Values.size();
      m_Values.addElement(store);
      m_Hashtable.put(store, new Integer(intIndex));
      return intIndex;
    }
  }

  /**
   * Adds a relation to a relation-valued attribute.
   *
   * @param value The value to add
   * @return the index assigned to the value, or -1 if the attribute is not
   * of type Attribute.RELATIONAL 
   */
  int addRelation(Instances value) {

    if (!isRelationValued()) {
      return -1;
    }
    if (!m_Header.equalHeaders(value)) {
      throw new IllegalArgumentException("Incompatible value for " +
                                         "relation-valued attribute.");
    }
    Integer index = (Integer)m_Hashtable.get(value);
    if (index != NULL) {
      return index.intValue();
    } else {
      int intIndex = m_Values.size();
      m_Values.addElement(value);
      m_Hashtable.put(value, new Integer(intIndex));
      return intIndex;
    }
  }

  /**
   * Adds an attribute value. Creates a fresh list of attribute
   * values before adding it.
   *
   * @param value the attribute value
   */
  void addValue(string value) {

    m_Values = (FastVector)m_Values.copy();
    m_Hashtable = (Hashtable)m_Hashtable.clone();
    forceAddValue(value);
  }

  /**
   * Produces a shallow copy of this attribute with a new name.
   *
   * @param newName the name of the new attribute
   * @return a copy of this attribute with the same index
   */
  //@ requires newName != NULL;
  //@ ensures \result.m_Name  == newName;
  //@ ensures \result.m_Index == m_Index;
  //@ ensures \result.m_Type  == m_Type;
  /*@ pure non_NULL @*/ Attribute copy(string newName) {

    Attribute copy = new Attribute(newName);

    copy.m_Index = m_Index;
    copy.m_DateFormat = m_DateFormat;
    copy.m_Type = m_Type;
    copy.m_Values = m_Values;
    copy.m_Hashtable = m_Hashtable;
    copy.m_Header = m_Header;
    copy.setMetadata(m_Metadata);
 
    return copy;
  }

  /**
   * Removes a value of a nominal, string, or relation-valued
   * attribute. Creates a fresh list of attribute values before
   * removing it.
   *
   * @param index the value's index
   * @throws IllegalArgumentException if the attribute is not 
   * of the correct type
   */
  //@ requires isNominal() || isString() || isRelationValued();
  //@ requires 0 <= index && index < m_Values.size();
  void delete(int index); 

  /**
   * Adds an attribute value.
   *
   * @param value the attribute value
   */
  //@ requires value != NULL;
  //@ ensures  m_Values.size() == \old(m_Values.size()) + 1;
  void forceAddValue(string value) {

    Object store = value;
    if (value.length() > STRING_COMPRESS_THRESHOLD) {
      try {
        store = new SerializedObject(value, true);
      } catch (Exception ex) {
        cout << "Couldn't compress string attribute value -"
	     << " storing uncompressed." << endl;
      }
    }
    m_Values.addElement(store);
    m_Hashtable.put(store, new Integer(m_Values.size() - 1));
  }

  /**
   * Sets the index of this attribute.
   *
   * @param index the index of this attribute
   */
  //@ requires 0 <= index;
  //@ assignable m_Index;
  //@ ensures m_Index == index;
  void setIndex(int index) {

    m_Index = index;
  }

  /**
   * Sets a value of a nominal attribute or string attribute.
   * Creates a fresh list of attribute values before it is set.
   *
   * @param index the value's index
   * @param string the value
   * @throws IllegalArgumentException if the attribute is not nominal or 
   * string.
   */
  //@ requires string != NULL;
  //@ requires isNominal() || isString();
  //@ requires 0 <= index && index < m_Values.size();
  void setValue(int index, string string); 

  /**
   * Sets a value of a relation-valued attribute.
   * Creates a fresh list of attribute values before it is set.
   *
   * @param index the value's index
   * @param data the value
   * @throws IllegalArgumentException if the attribute is not 
   * relation-valued.
   */
  void setValue(int index, Instances data) {
    
    if (isRelationValued()) { 
      if (!data.equalHeaders(m_Header)) {
        throw new IllegalArgumentException(string("Can't set relational value. ") +
                                           "Headers not compatible.");
      }
      m_Values = (FastVector)m_Values.copy();
      m_Values.setElementAt(data, index);
    } else {
      throw new IllegalArgumentException(string("Can only set value for")
                                         + " relation-valued attributes!");
    }
  }

  /**
   * Returns the given amount of milliseconds formatted according to the
   * current Date format.
   * 
   * @param date 	the date, represented in milliseconds since 
   * 			January 1, 1970, 00:00:00 GMT, to return as string
   * @return 		the formatted date
   */
  //@ requires isDate();
  /*@pure@*/ string formatDate(double date) {
    switch (m_Type) {
    case DATE:
      return m_DateFormat.format(new Date((long)date));
    default:
      throw new IllegalArgumentException(string("Can only format date")
						+ " values for date attributes!");
    }
  }

  /**
   * Parses the given string as Date, according to the current format and
   * returns the corresponding amount of milliseconds.
   * 
   * @param string the date to parse
   * @return the date in milliseconds since January 1, 1970, 00:00:00 GMT
   * @throws ParseException if parsing fails
   */
  //@ requires isDate();
  //@ requires string != NULL;
  double parseDate(string string) throws ParseException {
    switch (m_Type) {
    case DATE:
      long time = m_DateFormat.parse(string).getTime();
      // TODO put in a safety check here if we can't store the value in a double.
      return (double)time;
    default:
      throw new IllegalArgumentException(string("Can only parse date values ")
					 + "for date attributes!");
    }
  }

  /**
   * Returns the properties supplied for this attribute.
   *
   * @return metadata for this attribute
   */  
  /*@ pure @*/ ProtectedProperties getMetadata() {

    return m_Metadata;
  }

  /**
   * Returns the ordering of the attribute. One of the following:
   * 
   * ORDERING_SYMBOLIC - attribute values should be treated as symbols.
   * ORDERING_ORDERED  - attribute values have a global ordering.
   * ORDERING_MODULO   - attribute values have an ordering which wraps.
   *
   * @return the ordering type of the attribute
   */
  /*@ pure @*/ int ordering() {

    return m_Ordering;
  }

  /**
   * Returns whether the attribute values are equally spaced.
   *
   * @return whether the attribute is regular or not
   */
  /*@ pure @*/ bool isRegular() {

    return m_IsRegular;
  }

  /**
   * Returns whether the attribute can be averaged meaningfully.
   *
   * @return whether the attribute can be averaged or not
   */
  /*@ pure @*/ bool isAveragable() {

    return m_IsAveragable;
  }

  /**
   * Returns whether the attribute has a zeropoint and may be
   * added meaningfully.
   *
   * @return whether the attribute has a zeropoint or not
   */
  /*@ pure @*/ bool hasZeropoint() {

    return m_HasZeropoint;
  }

  /**
   * Returns the attribute's weight.
   *
   * @return the attribute's weight as a double
   */
  /*@ pure @*/ double weight() {

    return m_Weight;
  }

  /**
   * Sets the new attribute's weight
   * 
   * @param value	the new weight
   */
  void setWeight(double value); 
  
  /**
   * Returns the lower bound of a numeric attribute.
   *
   * @return the lower bound of the specified numeric range
   */
  /*@ pure @*/ double getLowerNumericBound() {

    return m_LowerBound;
  }

  /**
   * Returns whether the lower numeric bound of the attribute is open.
   *
   * @return whether the lower numeric bound is open or not (closed)
   */
  /*@ pure @*/ bool lowerNumericBoundIsOpen() {

    return m_LowerBoundIsOpen;
  }

  /**
   * Returns the upper bound of a numeric attribute.
   *
   * @return the upper bound of the specified numeric range
   */
  /*@ pure @*/ double getUpperNumericBound() {

    return m_UpperBound;
  }

  /**
   * Returns whether the upper numeric bound of the attribute is open.
   *
   * @return whether the upper numeric bound is open or not (closed)
   */
  /*@ pure @*/ bool upperNumericBoundIsOpen() {

    return m_UpperBoundIsOpen;
  }

  /**
   * Determines whether a value lies within the bounds of the attribute.
   *
   * @param value the value to check
   * @return whether the value is in range
   */
  /*@ pure @*/ bool isInRange(double value); 

  /**
   * Sets the metadata for the attribute. Processes the strings stored in the
   * metadata of the attribute so that the properties can be set up for the
   * easy-access metadata methods. Any strings sought that are omitted will
   * cause default values to be set.
   * 
   * The following properties are recognised:
   * ordering, averageable, zeropoint, regular, weight, and range.
   *
   * All other properties can be queried and handled appropriately by classes
   * calling the getMetadata() method.
   *
   * @param metadata the metadata
   * @throws IllegalArgumentException if the properties are not consistent
   */
  //@ requires metadata != NULL;
private: 
  void setMetadata(ProtectedProperties metadata); 

  /**
   * Sets the numeric range based on a string. If the string is NULL the range
   * will default to [-inf,+inf]. A square brace represents a closed interval, a
   * curved brace represents an open interval, and 'inf' represents infinity.
   * Examples of valid range strings: "[-inf,20)","(-13.5,-5.2)","(5,inf]"
   *
   * @param rangestring the string to parse as the attribute's numeric range
   * @throws IllegalArgumentException if the range is not valid
   */
  //@ requires rangestring != NULL;
  void setNumericRange(string rangeString); 
  
public:
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 5975 $");
  }
};
