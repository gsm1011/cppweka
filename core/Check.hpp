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

#ifndef _CPP_WEKA_CHECK_H_
#define _CPP_WEKA_CHECK_H_

// import java.util.Enumeration;
// import java.util.Vector;

/**
 * Abstract general class for testing in Weka.
 *
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.2 $
 */
class Check : public OptionHandler,
	      public RevisionHandler {
  
  /** Debugging mode, gives extra output if true */
protected:
  bool m_Debug = false;
  
  /** Silent mode, for no output at all to stdout */
  bool m_Silent = false;
  
  /**
   * Returns an enumeration describing the available options.
   *
   * @return an enumeration of all the available options.
   */
public:
    Enumeration listOptions();
  
  /**
   * Parses a given list of options. 
   *
   * @param options the list of options as an array of strings
   * @throws Exception if an option is not supported
   */
  inline void setOptions(String[] options) throws Exception {
    setDebug(Utils.getFlag('D', options));

    setSilent(Utils.getFlag('S', options));
  }
  
  /**
   * Gets the current settings of the CheckClassifier.
   *
   * @return an array of strings suitable for passing to setOptions
   */
    String[] getOptions();
  
  /**
   * Tries to instantiate a new instance of the given class and checks whether
   * it is an instance of the specified class. For convenience one can also
   * specify a classname prefix (e.g., "weka.classifiers") to avoid long 
   * classnames and then instantiate it with the shortened classname (e.g.,
   * "trees.J48").
   * 
   * @param prefix	the classname prefix (without trailing dot)
   * @param cls		the class to check whether the generated object is an
   * 			instance of
   * @param classname	the classname to instantiate
   * @param options	optional options for the object
   * @return		the configured object
   * @throws Exception	if instantiation fails
   */
protected:
  Object forName(string prefix, Class cls, string classname, 
		 String[] options); 
  
public:
  /**
   * Begin the tests, reporting results to System.out
   */
  virtual void doTests();
  
  /**
   * Set debugging mode
   *
   * @param debug true if debug output should be printed
   */
    void setDebug(bool debug);
  
  /**
   * Get whether debugging is turned on
   *
   * @return true if debugging output is on
   */
  inline bool getDebug() {
    return m_Debug;
  }
  
  /**
   * Set slient mode, i.e., no output at all to stdout
   *
   * @param value whether silent mode is active or not
   */
  inline void setSilent(bool value) {
    m_Silent = value;
  }
  
  /**
   * Get whether silent mode is turned on
   *
   * @return true if silent mode is on
   */
  inline bool getSilent() {
    return m_Silent;
  }
  
protected:
  /**
   * prints the given message to stdout, if not silent mode
   * 
   * @param msg         the text to print to stdout
   */
  inline void print(Object msg) {
    if (!getSilent())
      System.out.print(msg);
  }
  
  /**
   * prints the given message (+ LF) to stdout, if not silent mode
   * 
   * @param msg         the message to println to stdout
   */
  inline void println(Object msg) {
    print(msg + "\n");
  }
  
  /**
   * prints a LF to stdout, if not silent mode
   */
  inline void println() {
    print("\n");
  }
  
  /**
   * runs the CheckScheme with the given options
   * 
   * @param check	the checkscheme to setup and run
   * @param options	the commandline parameters to use
   */
    static void runCheck(Check check, String[] options);
};
