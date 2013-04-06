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

// import java.beans.BeanInfo;
// import java.beans.Introspector;
// import java.beans.PropertyDescriptor;
// import java.util.Collections;
// import java.util.Enumeration;
// import java.util.HashSet;
// import java.util.Iterator;
// import java.util.Vector;

/**
 * Simple command line checking of classes that are editable in the GOE.<p/>
 *
 * Usage: <p/>
 * <code>
 *     CheckGOE -W classname -- test options
 * </code> <p/>
 *
 <!-- options-start -->
 * Valid options are: <p/>
 * 
 * <pre> -D
 *  Turn on debugging output.</pre>
 * 
 * <pre> -S
 *  Silent mode - prints nothing to stdout.</pre>
 * 
 * <pre> -ignored &lt;comma-separated list of properties&gt;
 *  Skipped properties.
 *  (default: capabilities,options)</pre>
 * 
 * <pre> -W
 *  Full name of the class analysed.
 *  eg: weka.classifiers.rules.ZeroR
 *  (default weka.classifiers.rules.ZeroR)</pre>
 * 
 <!-- options-end -->
 *
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.4 $
 */
class CheckGOE : public Check {
protected:
  /** the object to test */
  Object m_Object = new weka.classifiers.rules.ZeroR();
  
  /** whether the tests were successful */
  bool m_Success;
  
  /** properties that are skipped in the checkToolTips method 
   * @see #checkToolTips() */
  HashSet<String> m_IgnoredProperties = new HashSet<String>();
  
  /**
   * default constructor
   */
public:
    CheckGOE();
  
  /**
   * Returns an enumeration describing the available options.
   *
   * @return 		an enumeration of all the available options.
   */
    Enumeration listOptions();
  
  /**
   * Parses a given list of options. <p/>
   *
   <!-- options-start -->
   * Valid options are: <p/>
   * 
   * <pre> -D
   *  Turn on debugging output.</pre>
   * 
   * <pre> -S
   *  Silent mode - prints nothing to stdout.</pre>
   * 
   * <pre> -ignored &lt;comma-separated list of properties&gt;
   *  Skipped properties.
   *  (default: capabilities,options)</pre>
   * 
   * <pre> -W
   *  Full name of the class analysed.
   *  eg: weka.classifiers.rules.ZeroR
   *  (default weka.classifiers.rules.ZeroR)</pre>
   * 
   <!-- options-end -->
   *
   * @param options 	the list of options as an array of strings
   * @throws Exception 	if an option is not supported
   */
    void setOptions(String[] options); 
  
  /**
   * Gets the current settings of the object.
   *
   * @return 		an array of strings suitable for passing to setOptions
   */
    String[] getOptions();
  
  /**
   * Set the object to work on.. 
   *
   * @param value 	the object to use.
   */
  inline void setObject(Object value) {
    m_Object = value;
  }
  
  /**
   * Get the object used in the tests.
   *
   * @return 		the object used in the tests.
   */
  inline Object getObject() {
    return m_Object;
  }

  /**
   * Sets the properties to ignore in checkToolTips(). Comma-separated list.
   * 
   * @param value	the list of properties
   * @see 		#checkToolTips()
   */
    void setIgnoredProperties(string value);

  /**
   * Get the ignored properties used in checkToolTips() as comma-separated 
   * list (sorted).
   * 
   * @return		the ignored properties
   * @see		#checkToolTips()
   */
    string getIgnoredProperties();
  
  /**
   * returns the success of the tests
   * 
   * @return		true if the tests were successful
   */
  inline bool getSuccess() {
    return m_Success;
  }

  /**
   * checks whether the object declares a globalInfo method.
   * 
   * @return 		true if the test was passed
   */
    bool checkGlobalInfo();

  /**
   * checks whether the object declares tip text method for all its
   * properties.
   * 
   * @return 		true if the test was passed
   */
    bool checkToolTips();
  
  /**
   * Runs some diagnostic tests on the object. Output is
   * printed to System.out (if not silent).
   */
    void doTests(); 
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  inline string getRevision() {
    return RevisionUtils.extract("$Revision: 1.4 $");
  }
  
  /** 
   * Main method for using the CheckGOE.
   *
   * @param args 	the options to the CheckGOE
   */
    static void main(String[] args); 
};
