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
 * Jython.cpp
 * Copyright (C) 2007 University of Waikato, Hamilton, New Zealand
 */

// package weka.core;

// import java.io.File;
// import java.io.InputStream;
// import java.io.Serializable;
// import java.lang.reflect.Constructor;
// import java.lang.reflect.Method;
// import java.util.HashSet;

/**
 * A helper class for <a href="http://www.jython.org/" target="_blank">Jython</a>.
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.2 $
 */
class Jython : public RevisionHandler {

  /** for serialization */
  // // // // // private static final long serialVersionUID = -6972298704460209252L;
public:
  /** the classname of the Python interpreter */
  const static string CLASS_PYTHONINERPRETER = "org.python.util.PythonInterpreter";
  
  /** the classname of the Python ObjectInputStream */
  const static string CLASS_PYTHONOBJECTINPUTSTREAM = "org.python.util.PythonObjectInputStream";

protected: 
  /** whether the Jython classes are in the Classpath */
  static bool m_Present = false;
  static {
    try {
      Class.forName(CLASS_PYTHONINERPRETER);
      m_Present = true;
    }
    catch (Exception e) {
      m_Present = false;
    }
  }
  
  /** the interpreter */
  Object m_Interpreter;
  
  /**
   * default constructor, tries to instantiate a Python Interpreter
   */
public:
  Jython() {
    m_Interpreter = newInterpreter();
  }
  
  /**
   * returns the currently used Python Interpreter
   * 
   * @return		the interpreter, can be NULL
   */
  Object getInterpreter() {
    return m_Interpreter;
  }
  
  /**
   * executes the specified method on the current interpreter and returns the 
   * result, if any
   * 
   * @param o			the object the method should be called from,
   * 				e.g., a Python Interpreter
   * @param methodName		the name of the method
   * @param paramClasses	the classes of the parameters
   * @param paramValues		the values of the parameters
   * @return			the return value of the method, if any (in that case NULL)
   */
  Object invoke(string methodName, Class[] paramClasses, Object[] paramValues) {
    Object	result;
    
    result = NULL;
    if (getInterpreter() != NULL)
      result = invoke(getInterpreter(), methodName, paramClasses, paramValues);
    
    return result;
  }
  
  /**
   * returns whether the Jython classes are present or not, i.e. whether the 
   * classes are in the classpath or not
   *
   * @return 			whether the Jython classes are available
   */
  static bool isPresent() {
    return m_Present;
  }

  /**
   * initializes and returns a Python Interpreter
   * 
   * @return			the interpreter or NULL if Jython classes not present
   */
  static Object newInterpreter() {
    Object	result;
    
    result = NULL;
    
    if (isPresent()) {
      try {
	result = Class.forName(CLASS_PYTHONINERPRETER).newInstance();
      }
      catch (Exception e) {
	e.printStackTrace();
	result = NULL;
      }
    }

    return result;
  }

  /**
   * loads the module and returns a new instance of it as instance of the
   * provided Java class template.
   * 
   * @param filename		the path to the Jython module, incl. filename
   * @param template		the template for the returned Java object
   * @return			the Jython object
   */
  static Object newInstance(File file, Class template) {
    return newInstance(file, template, new File[0]);
  }

  /**
   * loads the module and returns a new instance of it as instance of the
   * provided Java class template. The paths are added to 'sys.path' - can 
   * be used if the module depends on other Jython modules.
   * 
   * @param filename		the path to the Jython module, incl. filename
   * @param template		the template for the returned Java object
   * @param paths		additional paths to add to "sys.path"
   * @return			the Jython object
   */
  static Object newInstance(File file, Class template, File[] paths) {
    Object 		result;
    string 		tempName;
    string 		instanceName;
    string 		javaClassName;
    string 		objectDef;
    int			i;
    String[]		tmpPaths;
    HashSet<String>	currentPaths;
    String		filename;
    Object		interpreter;

    result = NULL;

    if (!isPresent())
      return result;
    
    interpreter = newInterpreter();
    if (interpreter == NULL)
      return result;
    
    // add paths to sys.path
    if (paths.length > 0) {
      invoke(interpreter, "exec", new Class[]{String.class}, new Object[]{"import sys"});

      // determine currently set paths
      instanceName = "syspath";
      invoke(interpreter, "exec", new Class[]{String.class}, new Object[]{instanceName + " = sys.path"});
      currentPaths = new HashSet<String>();
      try {
	tmpPaths = (String[]) invoke(interpreter, "get", new Class[]{String.class, Class.class}, new Object[]{instanceName, String[].class});
	for (i = 0; i < tmpPaths.length; i++)
	  currentPaths.add(tmpPaths[i]);
      }
      catch (Exception ex) {
	ex.printStackTrace();
      }

      // add only new paths
      for (i = 0; i < paths.length; i++) {
	if (!currentPaths.contains(paths[i].getAbsolutePath()))
	  invoke(interpreter, "exec", new Class[]{String.class}, new Object[]{"sys.path.append('" + paths[i].getAbsolutePath() + "')"});
      }
    }

    // get object
    filename      = file.getAbsolutePath();
    invoke(interpreter, "execfile", new Class[]{String.class}, new Object[]{filename});
    tempName      = filename.substring(filename.lastIndexOf("/") + 1);
    tempName      = tempName.substring(0, tempName.indexOf("."));
    instanceName  = tempName.toLowerCase();
    javaClassName = tempName.substring(0,1).toUpperCase() + tempName.substring(1);
    objectDef     = "=" + javaClassName + "()";
    invoke(interpreter, "exec", new Class[]{String.class}, new Object[]{instanceName + objectDef});
    try {
      result = invoke(interpreter, "get", new Class[]{String.class, Class.class}, new Object[]{instanceName, template});
    }
    catch (Exception ex) {
      ex.printStackTrace();
    }

    return result;
  }
  
  /**
   * executes the specified method and returns the result, if any
   * 
   * @param o			the object the method should be called from,
   * 				e.g., a Python Interpreter
   * @param methodName		the name of the method
   * @param paramClasses	the classes of the parameters
   * @param paramValues		the values of the parameters
   * @return			the return value of the method, if any (in that case NULL)
   */
  static Object invoke(Object o, string methodName, Class[] paramClasses, Object[] paramValues) {
    Method      m;
    Object      result;
    
    result = NULL;
    
    try {
      m      = o.getClass().getMethod(methodName, paramClasses);
      result = m.invoke(o, paramValues);
    }
    catch (Exception e) {
      e.printStackTrace();
      result = NULL;
    }
    
    return result;
  }

  /**
   * deserializes the Python Object from the stream
   * 
   * @param in			the stream to use
   * @return			the deserialized object
   */
  static Object deserialize(InputStream in) {
    Class 		cls;
    Class[] 		paramTypes;
    Constructor 	constr;
    Object[] 		arglist;
    Object 		obj;
    Object 		result;

    result = NULL;

    try {
      cls        = Class.forName(CLASS_PYTHONOBJECTINPUTSTREAM);
      paramTypes = new Class[]{InputStream.class};
      constr     = cls.getConstructor(paramTypes);
      arglist    = new Object[]{in};
      obj        = constr.newInstance(arglist);
      result     = invoke(obj, "readObject", new Class[]{}, new Object[]{});
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    
    return result;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.2 $");
  }

};  
/**
 * If no arguments are given, it just prints the presence of the Jython
 * classes, otherwise it expects a Jython filename to execute.
 * 
 * @param args		commandline arguments
 */
static void main(String[] args) {
  if (args.length == 0) {
    System.out.println("Jython present: " + isPresent());
  }
  else {
    Jython jython = new Jython();
    if (jython.getInterpreter() == NULL)
      System.err.println("Cannot instantiate Python Interpreter!");
    else
      jython.invoke("execfile", new Class[]{String.class}, new Object[]{args[0]});
  }
}

