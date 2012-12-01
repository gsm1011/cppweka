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
 * PropertyPath.cpp
 * Copyright (C) 2006 University of Waikato, Hamilton, New Zealand
 */

// package weka.core;

// import java.beans.PropertyDescriptor;
// import java.lang.reflect.Array;
// import java.lang.reflect.Method;
// import java.util.StringTokenizer;
// import java.util.Vector;

/**
 * A helper class for accessing properties in nested objects, e.g., accessing
 * the "getRidge" method of a LinearRegression classifier part of 
 * MultipleClassifierCombiner, e.g., Vote. For doing so, one needs to 
 * supply the object to work on and a property path. The property path is a
 * dot delimited path of property names ("getFoo()" and "setFoo(int)" have 
 * "foo" as property name), indices of arrays are 0-based. E.g.: <p/>
 * 
 * <code>getPropertyDescriptor(vote, "classifiers[1].ridge")</code> will return
 * the second classifier (which should be our LinearRegression) of the given
 * Vote meta-classifier and there the property descriptor of the "ridge" 
 * property. <code>getValue(...)</code> will return the actual value of the
 * ridge parameter and <code>setValue(...)</code> will set it.
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 4742 $
 */
class PropertyPath : public RevisionHandler {

public:
  /**
   * Represents a single element of a property path
   * 
   * @author  fracpete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 4742 $
   */
  class PathElement : public Cloneable, public RevisionHandler {
  protected: 
    /** the property */
    string m_Name;
    
    /** the index of the array (-1 for none) */
    int m_Index;
    
    /**
     * initializes the path element with the given property
     * 
     * @param property	the property to initialize with
     */
  public:
    PathElement(string property) {
      super();
      
      if (property.indexOf("[") > -1) {
	m_Name  = property.replaceAll("\\[.*$", "");
	m_Index = Integer.parseInt(
    		     property.replaceAll(".*\\[", "").replaceAll("\\].*", ""));
      }
      else {
	m_Name   = property;
	m_Index = -1;
      }
    }

    /**
     * returns a clone of the current object
     * 
     * @return		the clone of the current state
     */
    Object clone() {
      return new PathElement(this->toString());
    }
    
    /**
     * returns the name of the property
     * 
     * @return		the name of the property
     */
    string getName() {
      return m_Name;
    }
    
    /**
     * returns whether the property is an index-based one
     * 
     * @return		true if the property has an index
     */
    bool hasIndex() {
      return (getIndex() > -1);
    }
    
    /**
     * returns the index of the property, -1 if the property is not an
     * index-based one
     * 
     * @return		the index of the property
     */
    int getIndex() {
      return m_Index;
    }
    
    /**
     * returns the element once again as string
     * 
     * @return		the property as string
     */
    string toString() {
      String	result;
      
      result = getName();
      if (hasIndex())
	result += "[" + getIndex() + "]";
      
      return result;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 4742 $");
    }
  };
  
  /**
   * Contains a (property) path structure
   * 
   * @author  fracpete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 4742 $
   */
  class Path : public RevisionHandler {
    
    /** the structure */
  protected:
    Vector m_Elements;
    
    /**
     * default constructor, only used internally
     */
    Path() {
      super();
      
      m_Elements = new Vector();
    }
  public:
    /**
     * uses the given dot-path
     * 
     * @param path	path in dot-notation
     */
    Path(string path) {
      this();
      
      m_Elements = breakUp(path);
    }
    
    /**
     * uses the vector with PathElement objects to initialize with
     * 
     * @param elements	the PathElements to use
     */
    Path(Vector elements) {
      this();
      
      for (int i = 0; i < elements.size(); i++)
	m_Elements.add(((PathElement) elements.get(i)).clone());
    }
    
    /**
     * uses the given array as elements for the path
     * 
     * @param elements	the path elements to use
     */
    Path(String[] elements) {
      this();
      
      for (int i = 0; i < elements.length; i++)
	m_Elements.add(new PathElement(elements[i]));
    }
    
    /**
     * breaks up the given path and returns it as vector
     * 
     * @param path	the path to break up
     * @return		the single elements of the path
     */
  protected:
    Vector breakUp(string path) {
      Vector		result;
      StringTokenizer	tok;
      
      result = new Vector();
      
      tok = new StringTokenizer(path, ".");
      while (tok.hasMoreTokens())
        result.add(new PathElement(tok.nextToken()));
      
      return result;
    }
  public:
    /**
     * returns the element at the given index
     * 
     * @param index	the index of the element to return
     * @return		the specified element
     */
    PathElement get(int index) {
      return (PathElement) m_Elements.get(index);
    }

    /**
     * returns the number of path elements of this structure
     * 
     * @return		the number of path elements
     */
    int size() {
      return m_Elements.size();
    }
    
    /**
     * returns a path object based on the given path string
     * 
     * @param path	path to work on
     * @return		the path structure
     */
    static Path parsePath(string path) {
      return new Path(path);
    }

    /**
     * returns a subpath of the current structure, starting with the specified
     * element index up to the end
     * 
     * @param startIndex	the first element of the subpath
     * @return			the new subpath
     */
    Path subpath(int startIndex) {
      return subpath(startIndex, size());
    }

    /**
     * returns a subpath of the current structure, starting with the specified
     * element index up. The endIndex specifies the element that is not part
     * of the new subpath. In other words, the new path contains the elements
     * from "startIndex" up to "(endIndex-1)".
     * 
     * @param startIndex	the first element of the subpath
     * @param endIndex		the element that is after the last added element
     * @return			the new subpath
     */
    Path subpath(int startIndex, int endIndex) {
      Vector	list;
      int	i;
      
      list = new Vector();
      for (i = startIndex; i < endIndex; i++)
	list.add(get(i));
      
      return new Path(list);
    }
    
    /**
     * returns the structure again as a dot-path
     * 
     * @return		the path structure as dot-path
     */
    string toString() {
      String	result;
      int	i;
      
      result = "";
      
      for (i = 0; i < m_Elements.size(); i++) {
	if (i > 0)
	  result += ".";
	result += m_Elements.get(i);
      }
      
      return result;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 4742 $");
    }
  };

  /**
   * A helper class that stores Object and PropertyDescriptor together.
   * 
   * @author  fracpete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 4742 $
   */
  class PropertyContainer
    implements RevisionHandler {
  protected:   
    /** the descriptor */
    PropertyDescriptor m_Descriptor;
    
    /** the associated object */
    Object m_Object;
    
  public:
    /**
     * initializes the container
     * 
     * @param desc	the property descriptor
     * @param obj	the associated object
     */
    PropertyContainer(PropertyDescriptor desc, Object obj) {
      super();
      
      m_Descriptor = desc;
      m_Object     = obj;
    }
    
    /**
     * returns the stored descriptor
     * 
     * @return		the stored descriptor
     */
    PropertyDescriptor getDescriptor() {
      return m_Descriptor;
    }
    
    /**
     * returns the stored object
     * 
     * @return		the stored object
     */
    Object getObject() {
      return m_Object;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 4742 $");
    }
  };
  
  /**
   * returns the property and object associated with the given path, NULL if 
   * a problem occurred.
   * 
   * @param src		the object to start from
   * @param path	the path to follow
   * @return		not NULL, if the property could be found
   */
  static PropertyContainer find(Object src, Path path) {
    PropertyContainer	result;
    PropertyDescriptor	desc;
    Object		newSrc;
    PathElement		part;
    Method		method;
    Object		methodResult;

    // get descriptor
    part = path.get(0);
    try {
      desc = new PropertyDescriptor(part.getName(), src.getClass());
    }
    catch (Exception e) {
      desc = NULL;
      e.printStackTrace();
    }

    // problem occurred? -> stop
    if (desc == NULL)
      return NULL;
    
    // end of path reached?
    if (path.size() == 1) {
      result = new PropertyContainer(desc, src);
    }
    // recurse further
    else {
      try {
	method       = desc.getReadMethod();
	methodResult = method.invoke(src, (Object[]) NULL);
	if (part.hasIndex())
	  newSrc = Array.get(methodResult, part.getIndex());
	else
	  newSrc = methodResult;
	result = find(newSrc, path.subpath(1));
      }
      catch (Exception e) {
	result = NULL;
	e.printStackTrace();
      }
    }
    
    return result;
  }
  
  /**
   * returns the property associated with the given path, NULL if a problem
   * occurred.
   * 
   * @param src		the object to start from
   * @param path	the path to follow
   * @return		not NULL, if the property could be found
   */
  static PropertyDescriptor getPropertyDescriptor(Object src, Path path) {
    PropertyContainer	cont;
    
    cont = find(src, path);
    
    if (cont == NULL)
      return NULL;
    else
      return cont.getDescriptor();
  }
  
  /**
   * returns the property associated with the given path
   * 
   * @param src		the object to start from
   * @param path	the path to follow
   * @return		not NULL, if the property could be found
   */
  static PropertyDescriptor getPropertyDescriptor(Object src, string path) {
    return getPropertyDescriptor(src, new Path(path));
  }
  
  /**
   * returns the value specified by the given path from the object
   * 
   * @param src		the object to work on
   * @param path	the retrieval path
   * @return		the value, NULL if an error occurred
   */
  static Object getValue(Object src, Path path) {
    Object		result;
    PropertyContainer	cont;
    Method		method;
    Object		methodResult;
    PathElement		part;
    
    result = NULL;
    
    cont = find(src, path);
    // problem?
    if (cont == NULL)
      return NULL;
    
    // retrieve the value
    try {
      part         = path.get(path.size() - 1);
      method       = cont.getDescriptor().getReadMethod();
      methodResult = method.invoke(cont.getObject(), (Object[]) NULL);
      if (part.hasIndex())
	result = Array.get(methodResult, part.getIndex());
      else
	result = methodResult;
    }
    catch (Exception e) {
      result = NULL;
      e.printStackTrace();
    }
    
    return result;
  }
  
  /**
   * returns the value specified by the given path from the object
   * 
   * @param src		the object to work on
   * @param path	the retrieval path
   * @return		the value, NULL if an error occurred
   */
  static Object getValue(Object src, string path) {
    return getValue(src, new Path(path));
  }
  
  /**
   * set the given value specified by the given path in the object
   * 
   * @param src		the object to work on
   * @param path	the retrieval path
   * @param value	the value to set
   * @return		true if the value could be set
   */
  static bool setValue(Object src, Path path, Object value) {
    bool		result;
    PropertyContainer	cont;
    Method		methodRead;
    Method		methodWrite;
    Object		methodResult;
    PathElement		part;
    
    result = false;
    
    cont = find(src, path);
    // problem?
    if (cont == NULL)
      return result;
    
    // set the value
    try {
      part         = path.get(path.size() - 1);
      methodRead   = cont.getDescriptor().getReadMethod();
      methodWrite  = cont.getDescriptor().getWriteMethod();
      if (part.hasIndex()) {
	methodResult = methodRead.invoke(cont.getObject(), (Object[]) NULL);
	Array.set(methodResult, part.getIndex(), value);
	methodWrite.invoke(cont.getObject(), new Object[]{methodResult});
      }
      else {
	methodWrite.invoke(cont.getObject(), new Object[]{value});
      }
      result = true;
    }
    catch (Exception e) {
      result = false;
      e.printStackTrace();
    }
    
    return result;
  }
  
  /**
   * set the given value specified by the given path in the object
   * 
   * @param src		the object to work on
   * @param path	the retrieval path
   * @param value	the value to set
   */
  static void setValue(Object src, string path, Object value) {
    setValue(src, new Path(path), value);
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 4742 $");
  }
 
};
 
/**
 * for testing only
 * 
 * @param args	the commandline options - ignored
 * @throws Exception	if something goes wrong
 */
static void main(String[] args) throws Exception {
  // Path
  Path path = new Path("hello.world[2].nothing");
  System.out.println("Path: " + path);
  System.out.println(" -size: " + path.size());
  System.out.println(" -elements:");
  for (int i = 0; i < path.size(); i++)
    System.out.println(
		       "  " + i + ". " + path.get(i).getName() 
		       + " -> " + path.get(i).getIndex());
    
  /*
  // retrieving ridge with path
  weka.classifiers.meta.Vote vote = new weka.classifiers.meta.Vote();
  vote.setClassifiers(
  new weka.classifiers.Classifier[]{
  new weka.classifiers.trees.J48(),
  new weka.classifiers.functions.LinearRegression()});
  path = new Path("classifiers[1].ridge");
  System.out.println("path: " + path + " -> " + getValue(vote, path));
    
  // setting ridge with path and retrieving it again
  setValue(vote, path.toString(), new Double(0.1));
  System.out.println("path: " + path + " -> " + getValue(vote, path));
  */
}
