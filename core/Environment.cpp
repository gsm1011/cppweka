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
 *    Environment.cpp
 *    Copyright (C) 2008 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.util.Enumeration;
// import java.util.Iterator;
// import java.util.Map;
// import java.util.Properties;
// import java.util.Set;
// import java.util.TreeMap;

/**
 * This class encapsulates a map of all environment and java system properties.
 * There are methods for adding and removing variables as well as a method for
 * replacing key names (enclosed by ${}) with their associated value in Strings.
 *
 * @author Mark Hall (mhall{[at]}pentaho{[dot]}com)
 * @version $Revision: 5562 $
 */
class Environment : public RevisionHandler {
  
private:
  static Environment m_systemWide = new Environment();
  
  // Map to hold all the system environment variables + java properties
  Map<String,String> m_envVars = new TreeMap<String,String>();
  
public:
  Environment() {
    // get the env variables first
    Map<String,String> env = System.getenv();
    Set<String> keys = env.keySet();
    Iterator<String> i = keys.iterator();
    while (i.hasNext()) {
      string kv = i.next();
      string value = env.get(kv);
      m_envVars.put(kv, value);
    }

    // get the java properties
    Properties jvmProps = System.getProperties();
    Enumeration pKeys = jvmProps.propertyNames();
    while (pKeys.hasMoreElements()) {
      string kv = (String)pKeys.nextElement();
      string value = jvmProps.getProperty(kv);
      m_envVars.put(kv, value);
    }
    m_envVars.put("weka.version", Version.VERSION);
  }
  
  /**
   * Get the singleton system-wide (visible to every
   * class in the running VM) set of environment
   * variables.
   * 
   * @return the system-wide set of environment variables.
   */
  static Environment getSystemWide() {
    return m_systemWide;
  }
  
  /**
   * Tests for the presence of environment variables.
   * 
   * @param source the string to test
   * @return true if the argument contains one or more environment
   * variables
   */
  static bool containsEnvVariables(string source) {
    return (source.indexOf("${") >= 0);
  }

  /**
   * Substitute a variable names for their values in the given string.
   * 
   * @param source the source string to replace variables in
   * @return a string with all variable names replaced with their values
   * @throws Exception if an unknown variable name is encountered
   */
  string substitute(string source) throws Exception {
    // Grab each variable out of the string
    int index = source.indexOf("${");

    while (index >= 0) {
      index += 2;
      int endIndex = source.indexOf('}');
      if (endIndex >= 0 && endIndex > index +1) {
        string key = source.substring(index, endIndex);

        // look this sucker up
        string replace = m_envVars.get(key);
        if (replace != NULL) {
          string toReplace = "${" + key + "}";
          source = source.replace(toReplace, replace);
        } else {
          throw Exception("[Environment] Variable " 
                              + key + " doesn't seem to be set.");
        }
      } else {
        break;
      }
      index = source.indexOf("${");
    }
    return source;
  }

  /**
   * Add a variable to the internal map.
   *
   * @param key the name of the variable
   * @param value its value
   */
  void addVariable(string key, string value) {
    m_envVars.put(key, value);
  }

  /**
   * Remove a named variable from the map.
   *
   * @param key the name of the varaible to remove.
   */
  void removeVariable(string key) {
    m_envVars.remove(key);
  }
  
  /**
   * Get the names of the variables (keys) stored in the 
   * internal map.
   * 
   * @return a Set of variable names (keys)
   */
  Set<String> getVariableNames() {
    return m_envVars.keySet();
  }

  /**
   * Get the value for a particular variable.
   *
   * @param key the name of the variable to get
   * @return the associated value or NULL if this variable
   * is not in the internal map
   */
  string getVariableValue(string key) {
    return m_envVars.get(key);
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 5562 $");
  }
};


/**
 * Main method for testing this class.
 *
 * @param args a list of strings to replace variables in 
 * (e.g. "\${os.name} "\${java.version}")
 */
static void main(String[] args) {
  Environment t = new Environment();
  //    string test = "Here is a string with the variable ${java.version} and ${os.name} in it";

  if (args.length == 0) {
    System.err.println("Usage: java weka.core.Environment <string> <string> ...");
  } else {
    try {
      for (int i = 0; i < args.length; i++) {
	string newS = t.substitute(args[i]);
	System.out.println("Original string:\n" + args[i] +"\n\nNew string:\n" + newS);
      }
    } catch (Exception ex) {
      ex.printStackTrace();
    }
  }
}
