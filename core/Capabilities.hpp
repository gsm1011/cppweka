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

#ifndef _CPPWEKA_CAPABILITIES_H_
#define _CPPWEKA_CAPABILITIES_H_

#include <iostream>

using namespace std; 

// import weka.core.converters.ConverterUtils.DataSource;

// import java.io.Serializable;
// import java.util.ArrayList;
// import java.util.Collections;
// import java.util.HashSet;
// import java.util.Iterator;
// import java.util.List;
// import java.util.Properties;
// import java.util.Vector;

/**
 * A class that describes the capabilites (e.g., handling certain types of
 * attributes, missing values, types of classes, etc.) of a specific
 * classifier. By default, the classifier is capable of nothing. This
 * ensures that new features have to be enabled explicitly. <p/>
 * 
 * A common code fragment for making use of the capabilities in a classifier 
 * would be this:
 * <pre>
 * public void <b>buildClassifier</b>(Instances instances) throws Exception {
 *   // can the classifier handle the data?
 *   getCapabilities().<b>testWithFail(instances)</b>;
 *   ...
 *   // possible deletion of instances with missing class labels, etc.
 * </pre>
 * For only testing a single attribute, use this:
 * <pre>
 *   ...
 *   Attribute att = instances.attribute(0);
 *   getCapabilities().<b>testWithFail(att)</b>;
 *   ...
 * </pre>
 * Or for testing the class attribute (uses the capabilities that are 
 * especially for the class):
 * <pre>
 *   ...
 *   Attribute att = instances.classAttribute();
 *   getCapabilities().<b>testWithFail(att, <i>true</i>)</b>;
 *   ...
 * </pre>
 * 
 * @author  FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 6446 $
 */
class Capabilities : public RevisionHandler {
  
public:
  /** the properties file for managing the tests */
  const static string PROPERTIES_FILE = "weka/core/Capabilities.props";

  /** the actual properties */
protected:
  static Properties PROPERTIES;
  
  /** defines an attribute type */
  const static int ATTRIBUTE = 1;
  
private:
  /** defines a class type */
  const static int CLASS = 2;
  
  /** defines an attribute capability */
  const static int ATTRIBUTE_CAPABILITY = 4;
  
  /** defines a class capability */
  const static int CLASS_CAPABILITY = 8;
  
  /** defines a other capability */
  const static int OTHER_CAPABILITY = 16;

  /** enumeration of all capabilities */
public:
  enum Capability {
    // attributes
    /** can handle nominal attributes */
    NOMINAL_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Nominal attributes"),
    /** can handle binary attributes */
    BINARY_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Binary attributes"),
    /** can handle unary attributes */
    UNARY_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Unary attributes"),
    /** can handle empty nominal attributes */
    EMPTY_NOMINAL_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Empty nominal attributes"),
    /** can handle numeric attributes */
    NUMERIC_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Numeric attributes"),
    /** can handle date attributes */
    DATE_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Date attributes"),
    /** can handle string attributes */
    STRING_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "string attributes"),
    /** can handle relational attributes */
    RELATIONAL_ATTRIBUTES(ATTRIBUTE + ATTRIBUTE_CAPABILITY, "Relational attributes"),
    /** can handle missing values in attributes */
    MISSING_VALUES(ATTRIBUTE_CAPABILITY, "Missing values"),
    // class
    /** can handle data without class attribute, eg clusterers */
    NO_CLASS(CLASS_CAPABILITY, "No class"),
    /** can handle nominal classes */
    NOMINAL_CLASS(CLASS + CLASS_CAPABILITY, "Nominal class"),
    /** can handle binary classes */
    BINARY_CLASS(CLASS + CLASS_CAPABILITY, "Binary class"),
    /** can handle unary classes */
    UNARY_CLASS(CLASS + CLASS_CAPABILITY, "Unary class"),
    /** can handle empty nominal classes */
    EMPTY_NOMINAL_CLASS(CLASS + CLASS_CAPABILITY, "Empty nominal class"),
    /** can handle numeric classes */
    NUMERIC_CLASS(CLASS + CLASS_CAPABILITY, "Numeric class"),
    /** can handle date classes */
    DATE_CLASS(CLASS + CLASS_CAPABILITY, "Date class"),
    /** can handle string classes */
    STRING_CLASS(CLASS + CLASS_CAPABILITY, "string class"),
    /** can handle relational classes */
    RELATIONAL_CLASS(CLASS + CLASS_CAPABILITY, "Relational class"),
    /** can handle missing values in class attribute */
    MISSING_CLASS_VALUES(CLASS_CAPABILITY, "Missing class values"),
    // other
    /** can handle multi-instance data */
    ONLY_MULTIINSTANCE(OTHER_CAPABILITY, "Only multi-Instance data");

    /** the flags for the capabilities */
  private:
    int m_Flags = 0;
    
    /** the display string */
    string m_Display;
    
    /**
     * initializes the capability with the given flags
     * 
     * @param flags	"meta-data" for the capability
     * @param display	the display string (must be unique!)
     */
    inline Capability(int flags, string display):m_Flags(flags),m_Display(display) {
    }
    
    /**
     * returns true if the capability is an attribute
     * 
     * @return true if the capability is an attribute
     */
  public:
    inline bool isAttribute() {
      return ((m_Flags & ATTRIBUTE) == ATTRIBUTE);
    }
    
    /**
     * returns true if the capability is a class
     * 
     * @return true if the capability is a class
     */
    inline bool isClass() {
      return ((m_Flags & CLASS) == CLASS);
    }
    
    /**
     * returns true if the capability is an attribute capability
     * 
     * @return true if the capability is an attribute capability
     */
    inline bool isAttributeCapability() {
      return ((m_Flags & ATTRIBUTE_CAPABILITY) == ATTRIBUTE_CAPABILITY);
    }
    
    /**
     * returns true if the capability is a class capability
     * 
     * @return true if the capability is a class capability
     */
    inline bool isOtherCapability() {
      return ((m_Flags & OTHER_CAPABILITY) == OTHER_CAPABILITY);
    }
    
    /**
     * returns true if the capability is a other capability
     * 
     * @return true if the capability is a other capability
     */
    inline bool isClassCapability() {
      return ((m_Flags & CLASS_CAPABILITY) == CLASS_CAPABILITY);
    }
    
    /**
     * returns the display string of the capability
     * 
     * @return the display string
     */
    inline string toString() {
      return m_Display;
    }
  };

  /** the object that owns this capabilities instance */
protected:
  CapabilitiesHandler m_Owner;
  
  /** the hashset for storing the active capabilities */
  HashSet m_Capabilities;
  
  /** the hashset for storing dependent capabilities, eg for meta-classifiers */
  HashSet m_Dependencies;
  
  /** the reason why the test failed, used to throw an exception */
  Exception m_FailReason = NULL;

  /** the minimum number of instances in a dataset */
  int m_MinimumNumberInstances = 1;

  /** whether to perform any tests at all */
  bool m_Test;

  /** whether to perform data based tests */
  bool m_InstancesTest;

  /** whether to perform attribute based tests */
  bool m_AttributeTest;

  /** whether to test for missing values */
  bool m_MissingValuesTest;

  /** whether to test for missing class values */
  bool m_MissingClassValuesTest;

  /** whether to test for minimum number of instances */
  bool m_MinimumNumberInstancesTest;
  
public:
  /**
   * initializes the capabilities for the given owner
   * 
   * @param owner       the object that produced this Capabilities instance
   */
  Capabilities(CapabilitiesHandler owner) {
    super();

    setOwner(owner);
    m_Capabilities = new HashSet();
    m_Dependencies = new HashSet();

    // load properties
    if (PROPERTIES == NULL) {
      try {
        PROPERTIES = Utils.readProperties(PROPERTIES_FILE);
      }
      catch (Exception e) {
	e.printStackTrace();
	PROPERTIES = new Properties();
      }
    }
    
    m_Test                       = Boolean.parseBoolean(PROPERTIES.getProperty("Test", "true"));
    m_InstancesTest              = Boolean.parseBoolean(PROPERTIES.getProperty("InstancesTest", "true")) && m_Test;
    m_AttributeTest              = Boolean.parseBoolean(PROPERTIES.getProperty("AttributeTest", "true")) && m_Test;
    m_MissingValuesTest          = Boolean.parseBoolean(PROPERTIES.getProperty("MissingValuesTest", "true")) && m_Test;
    m_MissingClassValuesTest     = Boolean.parseBoolean(PROPERTIES.getProperty("MissingClassValuesTest", "true")) && m_Test;
    m_MinimumNumberInstancesTest = Boolean.parseBoolean(PROPERTIES.getProperty("MinimumNumberInstancesTest", "true")) && m_Test;
  }
  
  /**
   * retrieves the data from the given Capabilities object
   * 
   * @param c	  the capabilities object to initialize with
   */
  void assign(Capabilities c) {
    for (Capability cap: Capability.values()) {
      // capability
      if (c.handles(cap))
        enable(cap);
      else
	disable(cap);
      // dependency
      if (c.hasDependency(cap))
        enableDependency(cap);
      else
	disableDependency(cap);
    }

    setMinimumNumberInstances(c.getMinimumNumberInstances());
  }

  /**
   * performs an AND conjunction with the capabilities of the given 
   * Capabilities object and updates itself
   *
   * @param c     the capabilities to AND with
   */
  void and(Capabilities c) {
    for (Capability cap: Capability.values()) {
      // capability
      if (handles(cap) && c.handles(cap))
        m_Capabilities.add(cap);
      else
        m_Capabilities.remove(cap);
      // dependency
      if (hasDependency(cap) && c.hasDependency(cap))
        m_Dependencies.add(cap);
      else
        m_Dependencies.remove(cap);
    }
    
    // minimum number of instances that both handlers need at least to work
    if (c.getMinimumNumberInstances() > getMinimumNumberInstances())
      setMinimumNumberInstances(c.getMinimumNumberInstances());
  }

  /**
   * performs an OR conjunction with the capabilities of the given 
   * Capabilities object and updates itself
   *
   * @param c     the capabilities to OR with
   */
  void or(Capabilities c) {
    for (Capability cap: Capability.values()) {
      // capability
      if (handles(cap) || c.handles(cap))
        m_Capabilities.add(cap);
      else
        m_Capabilities.remove(cap);
      // dependency
      if (hasDependency(cap) || c.hasDependency(cap))
        m_Dependencies.add(cap);
      else
        m_Dependencies.remove(cap);
    }
    
    if (c.getMinimumNumberInstances() < getMinimumNumberInstances())
      setMinimumNumberInstances(c.getMinimumNumberInstances());
  }
  
  /**
   * Returns true if the currently set capabilities support at least all of
   * the capabiliites of the given Capabilities object (checks only the enum!)
   * 
   * @param c	the capabilities to support at least
   * @return	true if all the requested capabilities are supported
   */
  bool supports(Capabilities c) {
    bool	result;
    
    result = true;
    
    for (Capability cap: Capability.values()) {
      if (c.handles(cap) && !handles(cap)) {
	result = false;
	break;
      }
    }

    return result;
  }
  
  /**
   * Returns true if the currently set capabilities support (or have a 
   * dependency) at least all of the capabilities of the given Capabilities 
   * object (checks only the enum!)
   * 
   * @param c	the capabilities (or dependencies) to support at least
   * @return	true if all the requested capabilities are supported (or at 
   * 		least have a dependency)
   */
  bool supportsMaybe(Capabilities c) {
    bool	result;
    
    result = true;
    
    for (Capability cap: Capability.values()) {
      if (c.handles(cap) && !(handles(cap) || hasDependency(cap))) {
	result = false;
	break;
      }
    }

    return result;
  }

  /**
   * sets the owner of this capabilities object
   * 
   * @param value       the new owner
   */
  inline void setOwner(CapabilitiesHandler value) {
    m_Owner = value;
  }
  
  /**
   * returns the owner of this capabilities object
   * 
   * @return            the current owner of this capabilites object
   */
  inline CapabilitiesHandler getOwner() {
    return m_Owner;
  }

  /**
   * sets the minimum number of instances that have to be in the dataset
   * 
   * @param value       the minimum number of instances
   */
  inline void setMinimumNumberInstances(int value) {
    if (value >= 0)
      m_MinimumNumberInstances = value;
  }
  
  /**
   * returns the minimum number of instances that have to be in the dataset
   * 
   * @return            the minimum number of instances
   */
  inline int getMinimumNumberInstances() {
    return m_MinimumNumberInstances;
  }
  
  /**
   * Returns an Iterator over the stored capabilities
   * 
   * @return iterator over the current capabilities
   */
  inline Iterator capabilities() {
    return m_Capabilities.iterator();
  }
  
  /**
   * Returns an Iterator over the stored dependencies
   * 
   * @return iterator over the current dependencies
   */
  inline Iterator dependencies() {
    return m_Dependencies.iterator();
  }
  
  /**
   * enables the given capability. 
   * Enabling NOMINAL_ATTRIBUTES also enables BINARY_ATTRIBUTES, 
   * UNARY_ATTRIBUTES and EMPTY_NOMINAL_ATTRIBUTES. 
   * Enabling BINARY_ATTRIBUTES also enables UNARY_ATTRIBUTES and 
   * EMPTY_NOMINAL_ATTRIBUTES. 
   * Enabling UNARY_ATTRIBUTES also enables EMPTY_NOMINAL_ATTRIBUTES.
   * But NOMINAL_CLASS only enables BINARY_CLASS, since normal schemes in Weka
   * don't work with datasets that have only 1 class label (or none).
   *
   * @param c     the capability to enable
   */
  void enable(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      enable(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      enable(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      enable(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      enable(Capability.BINARY_CLASS);
    }

    m_Capabilities.add(c);
  }
  
  /**
   * enables the dependency flag for the given capability
   * Enabling NOMINAL_ATTRIBUTES also enables BINARY_ATTRIBUTES, 
   * UNARY_ATTRIBUTES and EMPTY_NOMINAL_ATTRIBUTES. 
   * Enabling BINARY_ATTRIBUTES also enables UNARY_ATTRIBUTES and 
   * EMPTY_NOMINAL_ATTRIBUTES. 
   * Enabling UNARY_ATTRIBUTES also enables EMPTY_NOMINAL_ATTRIBUTES.
   * But NOMINAL_CLASS only enables BINARY_CLASS, since normal schemes in Weka
   * don't work with datasets that have only 1 class label (or none).
   *
   * @param c     the capability to enable the dependency flag for
   */
  void enableDependency(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      enableDependency(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      enableDependency(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      enableDependency(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      enableDependency(Capability.BINARY_CLASS);
    }

    m_Dependencies.add(c);
  }
  
  /**
   * enables all class types
   * 
   * @see #disableAllClasses()
   * @see #getClassCapabilities()
   */
  void enableAllClasses() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	enable(cap);
    }
  }
  
  /**
   * enables all class type dependencies
   * 
   * @see #disableAllClassDependencies()
   * @see #getClassCapabilities()
   */
  void enableAllClassDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	enableDependency(cap);
    }
  }
  
  /**
   * enables all attribute types
   * 
   * @see #disableAllAttributes()
   * @see #getAttributeCapabilities()
   */
  void enableAllAttributes() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	enable(cap);
    }
  }
  
  /**
   * enables all attribute type dependencies
   * 
   * @see #disableAllAttributeDependencies()
   * @see #getAttributeCapabilities()
   */
  void enableAllAttributeDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	enableDependency(cap);
    }
  }
  
  /**
   * enables all attribute and class types (including dependencies)
   */
  void enableAll() {
    enableAllAttributes();
    enableAllAttributeDependencies();
    enableAllClasses();
    enableAllClassDependencies();
    enable(Capability.MISSING_VALUES);
    enable(Capability.MISSING_CLASS_VALUES);
  }

  /**
   * disables the given capability
   * Disabling NOMINAL_ATTRIBUTES also disables BINARY_ATTRIBUTES, 
   * UNARY_ATTRIBUTES and EMPTY_NOMINAL_ATTRIBUTES. 
   * Disabling BINARY_ATTRIBUTES also disables UNARY_ATTRIBUTES and 
   * EMPTY_NOMINAL_ATTRIBUTES. 
   * Disabling UNARY_ATTRIBUTES also disables EMPTY_NOMINAL_ATTRIBUTES.
   * The same hierarchy applies to the class capabilities.
   *
   * @param c     the capability to disable
   */
  void disable(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      disable(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      disable(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      disable(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      disable(Capability.BINARY_CLASS);
    }
    else if (c == Capability.BINARY_CLASS) {
      disable(Capability.UNARY_CLASS);
    }
    else if (c == Capability.UNARY_CLASS) {
      disable(Capability.EMPTY_NOMINAL_CLASS);
    }

    m_Capabilities.remove(c);
  }

  /**
   * disables the dependency of the given capability
   * Disabling NOMINAL_ATTRIBUTES also disables BINARY_ATTRIBUTES, 
   * UNARY_ATTRIBUTES and EMPTY_NOMINAL_ATTRIBUTES. 
   * Disabling BINARY_ATTRIBUTES also disables UNARY_ATTRIBUTES and 
   * EMPTY_NOMINAL_ATTRIBUTES. 
   * Disabling UNARY_ATTRIBUTES also disables EMPTY_NOMINAL_ATTRIBUTES.
   * The same hierarchy applies to the class capabilities.
   *
   * @param c     the capability to disable the dependency flag for
   */
  void disableDependency(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      disableDependency(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      disableDependency(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      disableDependency(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      disableDependency(Capability.BINARY_CLASS);
    }
    else if (c == Capability.BINARY_CLASS) {
      disableDependency(Capability.UNARY_CLASS);
    }
    else if (c == Capability.UNARY_CLASS) {
      disableDependency(Capability.EMPTY_NOMINAL_CLASS);
    }

    m_Dependencies.remove(c);
  }
  
  /**
   * disables all class types
   * 
   * @see #enableAllClasses()
   * @see #getClassCapabilities()
   */
  void disableAllClasses() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	disable(cap);
    }
  }
  
  /**
   * disables all class type dependencies
   * 
   * @see #enableAllClassDependencies()
   * @see #getClassCapabilities()
   */
  void disableAllClassDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	disableDependency(cap);
    }
  }
  
  /**
   * disables all attribute types
   * 
   * @see #enableAllAttributes()
   * @see #getAttributeCapabilities()
   */
  void disableAllAttributes() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	disable(cap);
    }
  }
  
  /**
   * disables all attribute type dependencies
   * 
   * @see #enableAllAttributeDependencies()
   * @see #getAttributeCapabilities()
   */
  void disableAllAttributeDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	disableDependency(cap);
    }
  }
  
  /**
   * disables all attribute and class types (including dependencies)
   */
  void disableAll() {
    disableAllAttributes();
    disableAllAttributeDependencies();
    disableAllClasses();
    disableAllClassDependencies();
    disable(Capability.MISSING_VALUES);
    disable(Capability.MISSING_CLASS_VALUES);
    disable(Capability.NO_CLASS);
  }
  
  /**
   * returns all class capabilities
   * 
   * @return		all capabilities regarding the class
   * @see #enableAllClasses()
   * @see #disableAllClasses()
   */
  Capabilities getClassCapabilities() {
    Capabilities	result;
    
    result = new Capabilities(getOwner());
    
    for (Capability cap: Capability.values()) {
      if (cap.isClassCapability()) {
	if (handles(cap))
	  result.m_Capabilities.add(cap);
      }
    }
    
    return result;
  }
  
  /**
   * returns all attribute capabilities
   * 
   * @return		all capabilities regarding attributes
   * @see #enableAllAttributes()
   * @see #disableAllAttributes()
   */
  Capabilities getAttributeCapabilities() {
    Capabilities	result;
    
    result = new Capabilities(getOwner());
    
    for (Capability cap: Capability.values()) {
      if (cap.isAttributeCapability()) {
	if (handles(cap))
	  result.m_Capabilities.add(cap);
      }
    }
    
    return result;
  }
  
  /**
   * returns all other capabilities, besides class and attribute related ones
   * 
   * @return		all other capabilities, besides class and attribute 
   * 			related ones
   */
  Capabilities getOtherCapabilities() {
    Capabilities	result;
    
    result = new Capabilities(getOwner());
    
    for (Capability cap: Capability.values()) {
      if (cap.isOtherCapability()) {
	if (handles(cap))
	  result.m_Capabilities.add(cap);
      }
    }
    
    return result;
  }

  /**
   * returns true if the classifier handler has the specified capability
   *
   * @param c     the capability to test
   * @return      true if the classifier handler has the capability
   */
  inline bool handles(Capability c) {
    return m_Capabilities.contains(c);
  }

  /**
   * returns true if the classifier handler has a dependency for the specified 
   * capability
   *
   * @param c     the capability to test
   * @return      true if the classifier handler has a dependency for the 
   *               capability
   */
  inline bool hasDependency(Capability c) {
    return m_Dependencies.contains(c);
  }
  
  /**
   * Checks whether there are any dependencies at all
   * 
   * @return true if there is at least one dependency for a capability
   */
  inline bool hasDependencies() {
    return (m_Dependencies.size() > 0);
  }

  /**
   * returns the reason why the tests failed, is NULL if tests succeeded
   * 
   * @return		the reason why the tests failed
   */
  inline Exception getFailReason() {
    return m_FailReason;
  }
  
  /**
   * Generates the message for, e.g., an exception. Adds the classname before the
   * actual message and returns that string.
   * 
   * @param msg		the actual content of the message, e.g., exception
   * @return		the new message
   */
protected:
  string createMessage(string msg) {
    String	result;
    
    result = "";
    
    if (getOwner() != NULL)
      result = getOwner().getClass().getName();
    else
      result = "<anonymous>";
      
    result += ": " + msg;
    
    return result;
  }
  
  /**
   * Test the given attribute, whether it can be processed by the handler,
   * given its capabilities. The method assumes that the specified attribute
   * is not the class attribute.
   * 
   * @param att		the attribute to test
   * @return		true if all the tests succeeded
   * @see		#test(Attribute, bool)
   */
public:
  bool test(Attribute att) {
    return test(att, false);
  }
  
  /**
   * Test the given attribute, whether it can be processed by the handler,
   * given its capabilities.
   * 
   * @param att		the attribute to test
   * @param isClass	whether this attribute is the class attribute
   * @return		true if all the tests succeeded
   * @see		#m_AttributeTest
   */
  bool test(Attribute att, bool isClass) {
    bool		result;
    Capability		cap;
    Capability		capBinary;
    Capability		capUnary;
    Capability		capEmpty;
    String		errorStr;
    
    result = true;
    
    // shall we test the data?
    if (!m_AttributeTest)
      return result;

    // for exception
    if (isClass)
      errorStr  = "class";
    else
      errorStr  = "attributes";
    
    switch (att.type()) {
      case Attribute.NOMINAL:
	if (isClass) {
	  cap       = Capability.NOMINAL_CLASS;
	  capBinary = Capability.BINARY_CLASS;
	  capUnary  = Capability.UNARY_CLASS;
	  capEmpty  = Capability.EMPTY_NOMINAL_CLASS;
	}
	else {
	  cap       = Capability.NOMINAL_ATTRIBUTES;
	  capBinary = Capability.BINARY_ATTRIBUTES;
	  capUnary  = Capability.UNARY_ATTRIBUTES;
	  capEmpty  = Capability.EMPTY_NOMINAL_ATTRIBUTES;
	}
	
        if (handles(cap) && (att.numValues() > 2))
          break;
        else if (handles(capBinary) && (att.numValues() == 2))
          break;
        else if (handles(capUnary) && (att.numValues() == 1))
          break;
        else if (handles(capEmpty) && (att.numValues() == 0))
          break;

        if (att.numValues() == 0) {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle empty nominal " + errorStr + "!"));
          result = false;
        }
        if (att.numValues() == 1) {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle unary " + errorStr + "!"));
          result = false;
        }
        else if (att.numValues() == 2) {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle binary " + errorStr + "!"));
          result = false;
        }
        else {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle multi-valued nominal " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.NUMERIC:
	if (isClass)
	  cap = Capability.NUMERIC_CLASS;
	else
	  cap = Capability.NUMERIC_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle numeric " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.DATE:
	if (isClass)
	  cap = Capability.DATE_CLASS;
	else
	  cap = Capability.DATE_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle date " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.STRING:
	if (isClass)
	  cap = Capability.STRING_CLASS;
	else
	  cap = Capability.STRING_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle string " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.RELATIONAL:
	if (isClass)
	  cap = Capability.RELATIONAL_CLASS;
	else
	  cap = Capability.RELATIONAL_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle relational " + errorStr + "!"));
          result = false;
        }
        // attributes in the relation of this attribute must be tested
        // separately with a different Capabilites object
        break;

      default:
        m_FailReason = new UnsupportedAttributeTypeException(
                            createMessage("Cannot handle unknown attribute type '" 
                                        + att.type() + "'!"));
        result = false;
    }
    
    return result;
  }
  
  /**
   * Tests the given data, whether it can be processed by the handler,
   * given its capabilities. Classifiers implementing the 
   * <code>MultiInstanceCapabilitiesHandler</code> interface are checked 
   * automatically for their multi-instance Capabilities (if no bags, then
   * only the bag-structure, otherwise only the first bag).
   *
   * @param data 	the data to test
   * @return		true if all the tests succeeded
   * @see 		#test(Instances, int, int)
   */
    bool test(Instances data);
  
  /**
   * Tests a certain range of attributes of the given data, whether it can be 
   * processed by the handler, given its capabilities. Classifiers 
   * implementing the <code>MultiInstanceCapabilitiesHandler</code> interface 
   * are checked automatically for their multi-instance Capabilities (if no 
   * bags, then only the bag-structure, otherwise only the first bag).
   *
   * @param data 	the data to test
   * @param fromIndex	the range of attributes - start (incl.)
   * @param toIndex	the range of attributes - end (incl.)
   * @return		true if all the tests succeeded
   * @see 		MultiInstanceCapabilitiesHandler
   * @see 		#m_InstancesTest
   * @see		#m_MissingValuesTest
   * @see		#m_MissingClassValuesTest
   * @see		#m_MinimumNumberInstancesTest
   */
    bool test(Instances data, int fromIndex, int toIndex);

  /**
   * tests the given attribute by calling the test(Attribute,bool) method 
   * and throws an exception if the test fails. The method assumes that the
   * specified attribute is not the class attribute.
   *
   * @param att        	the attribute to test
   * @throws Exception  in case the attribute doesn't pass the tests
   * @see 		#test(Attribute,bool)
   */
    void testWithFail(Attribute att); 

  /**
   * tests the given attribute by calling the test(Attribute,bool) method 
   * and throws an exception if the test fails.
   *
   * @param att        	the attribute to test
   * @param isClass	whether this attribute is the class attribute
   * @throws Exception  in case the attribute doesn't pass the tests
   * @see 		#test(Attribute,bool)
   */
    void testWithFail(Attribute att, bool isClass);

  /**
   * tests the given data by calling the test(Instances,int,int) method and 
   * throws an exception if the test fails.
   *
   * @param data        the data to test
   * @param fromIndex	the range of attributes - start (incl.)
   * @param toIndex	the range of attributes - end (incl.)
   * @throws Exception  in case the data doesn't pass the tests
   * @see 		#test(Instances,int,int)
   */
    void testWithFail(Instances data, int fromIndex, int toIndex) ; 

  /**
   * tests the given data by calling the test(Instances) method and throws 
   * an exception if the test fails.
   *
   * @param data        the data to test
   * @throws Exception  in case the data doesn't pass the tests
   * @see 		#test(Instances)
   */
    void testWithFail(Instances data); 
  
  /**
   * returns a string representation of the capabilities
   * 
   * @return 	a string representation of this object
   */
    string toString(); 
  
  /**
   * turns the capabilities object into source code. The returned source code
   * is a block that creates a Capabilities object named 'objectname' and
   * enables all the capabilities of this Capabilities object.
   * 
   * @param objectname	the name of the Capabilities object being instantiated
   * @return		the generated source code
   */
    string toSource(string objectname);
    
  /**
   * turns the capabilities object into source code. The returned source code
   * is a block that creates a Capabilities object named 'objectname' and
   * enables all the capabilities of this Capabilities object.
   * 
   * @param objectname	the name of the Capabilities object being instantiated
   * @param indent	the number of blanks to indent
   * @return		the generated source code
   */
    string toSource(string objectname, int indent);
  
  /**
   * returns a Capabilities object specific for this data. The multi-instance
   * capability is not checked as well as the minimum number of instances
   * is not set.
   * 
   * @param data	the data to base the capabilities on
   * @return		a data-specific capabilities object
   * @throws Exception	in case an error occurrs, e.g., an unknown attribute 
   * 			type
   */
    static Capabilities forInstances(Instances data);
  
  /**
   * returns a Capabilities object specific for this data. The minimum number 
   * of instances is not set, the check for multi-instance data is optional.
   * 
   * @param data	the data to base the capabilities on
   * @param multi	if true then the structure is checked, too
   * @return		a data-specific capabilities object
   * @throws Exception	in case an error occurrs, e.g., an unknown attribute 
   * 			type
   */
    static Capabilities forInstances(Instances data, bool multi); 
 
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  inline string getRevision() {
    return RevisionUtils.extract("$Revision: 6446 $");
  }

/**
 * loads the given dataset and prints the Capabilities necessary to 
 * process it. <p/>
 * 
 * Valid parameters: <p/>
 * 
 * -file filename <br/>
 *  the file to load
 *  
 * -c index
 *  the explicit index of the class attribute (default: none)
 * 
 * @param args	the commandline arguments
 * @throws Exception	if something goes wrong
 */
    static void main(String[] args); 

};

#endif  
