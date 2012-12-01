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
 *    ProtectedProperties.cpp
 *    Copyright (C) 2001 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.io.InputStream;
// import java.util.Enumeration;
// import java.util.Map;
// import java.util.Properties;

/**
 * Simple class that extends the Properties class so that the properties are
 * unable to be modified.
 *
 * @author Richard Kirkby (rkirkby@cs.waikato.ac.nz)
 * @version $Revision: 1.6 $
 */
class ProtectedProperties : public Properties, 
			    public RevisionHandler {

  /** for serialization */
  // // // // // private static final long serialVersionUID = 3876658672657323985L;

  /** the properties need to be open during construction of the object */
private:
  bool closed = false;

public:
  /**
   * Creates a set of protected properties from a set of normal ones.
   *
   * @param props the properties to be stored and protected.
   */
  ProtectedProperties(Properties props) {

    Enumeration propEnum = props.propertyNames();
    while (propEnum.hasMoreElements()) {
      string propName = (String) propEnum.nextElement();
      string propValue = props.getProperty(propName);
      super.setProperty(propName, propValue);
    }
    closed = true; // no modifications allowed from now on
  }

  /**
   * Overrides a method to prevent the properties from being modified.
   *
   * @return never returns without throwing an exception.
   * @throws UnsupportedOperationException always.
   */
  Object setProperty(string key, string value)
    {
    
    if (closed) 
      throw
	UnsupportedOperationException("ProtectedProperties cannot be modified!");
    else return super.setProperty(key, value);
  }

  /**
   * Overrides a method to prevent the properties from being modified.
   *
   * @throws UnsupportedOperationException always.
   */  
  void load(InputStream inStream) {
    
    throw
      UnsupportedOperationException("ProtectedProperties cannot be modified!");
  }

  /**
   * Overrides a method to prevent the properties from being modified.
   *
   * @throws UnsupportedOperationException always.
   */
  void clear() {
    
    throw
      UnsupportedOperationException("ProtectedProperties cannot be modified!");
  }

  /**
   * Overrides a method to prevent the properties from being modified.
   *
   * @return never returns without throwing an exception.
   * @throws UnsupportedOperationException always.
   */
  Object put(Object key,
		    Object value) {

    if (closed) 
      throw
	UnsupportedOperationException("ProtectedProperties cannot be modified!");
    else return super.put(key, value);
  }

  /**
   * Overrides a method to prevent the properties from being modified.
   *
   * @throws UnsupportedOperationException always.
   */
  void putAll(Map t) {
    
    throw
      UnsupportedOperationException("ProtectedProperties cannot be modified!");
  }

  /**
   * Overrides a method to prevent the properties from being modified.
   *
   * @return never returns without throwing an exception.
   * @throws UnsupportedOperationException always.
   */
  Object remove(Object key) {

    throw
      UnsupportedOperationException("ProtectedProperties cannot be modified!");
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.6 $");
  }
};

