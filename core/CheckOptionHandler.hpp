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

#ifndef _CPP_WEKA_CHECKOPTIONHANDLER_H_
#define _CPP_WEKA_CHECKOPTIONHANDLER_H_

#include <vector>
#include <iostream>

using namespace std; 

/**
 * Simple command line checking of classes that implement OptionHandler.<p/>
 *
 * Usage: <p/>
 * <code>
 *     CheckOptionHandler -W optionHandlerClassName -- test options
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
 * <pre> -W
 *  Full name of the OptionHandler analysed.
 *  eg: weka.classifiers.rules.ZeroR
 *  (default weka.classifiers.rules.ZeroR)</pre>
 * 
 * <pre> 
 * Options specific to option handler weka.classifiers.rules.ZeroR:
 * </pre>
 * 
 * <pre> -D
 *  If set, classifier is run in debug mode and
 *  may output additional info to the console</pre>
 * 
 <!-- options-end -->
 *
 * Options after -- are used as user options in testing the
 * OptionHandler
 *
 * @author Len Trigg (trigg@cs.waikato.ac.nz)
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.13 $
 */
class CheckOptionHandler : public Check {
protected:
    /** the optionhandler to test */
    OptionHandler m_OptionHandler = new weka.classifiers.rules.ZeroR();

    /** the user-supplied options */
    String[] m_UserOptions = new String[0];
  
    /** whether the tests were successful */
    bool m_Success;
  
    /**
     * Returns an enumeration describing the available options.
     *
     * @return an enumeration of all the available options.
     */
public:
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
     * <pre> -W
     *  Full name of the OptionHandler analysed.
     *  eg: weka.classifiers.rules.ZeroR
     *  (default weka.classifiers.rules.ZeroR)</pre>
     * 
     * <pre> 
     * Options specific to option handler weka.classifiers.rules.ZeroR:
     * </pre>
     * 
     * <pre> -D
     *  If set, classifier is run in debug mode and
     *  may output additional info to the console</pre>
     * 
     <!-- options-end -->
     *
     * @param options the list of options as an array of strings
     * @throws Exception if an option is not supported
     */
    void setOptions(String[] options);
  
    /**
     * Gets the current settings of the CheckClassifier.
     *
     * @return an array of strings suitable for passing to setOptions
     */
    String[] getOptions();
  
    /**
     * Set the OptionHandler to work on.. 
     *
     * @param value the OptionHandler to use.
     */
    inline void setOptionHandler(OptionHandler value) {
	m_OptionHandler = value;
    }
  
    /**
     * Get the OptionHandler used in the tests.
     *
     * @return the OptionHandler used in the tests.
     */
    inline OptionHandler getOptionHandler() {
	return m_OptionHandler;
    }

    /**
     * Sets the user-supplied options (creates a copy)
     * 
     * @param value	the user-supplied options to use
     */
    inline void setUserOptions(String[] value) {
	m_UserOptions = getCopy(value);
    }
  
    /**
     * Gets the current user-supplied options (creates a copy)
     * 
     * @return		the user-supplied options
     */
    inline String[] getUserOptions() {
	return getCopy(m_UserOptions);
    }
  
    /**
     * returns the success of the tests
     * 
     * @return		true if the tests were successful
     */
    inline bool getSuccess() {
	return m_Success;
    }
  
protected:
    /**
     * Prints the given options to a string.
     *
     * @param options the options to be joined
     * @return the options as one long string
     */
    string printOptions(String[] options);

    /**
     * Compares the two given sets of options.
     *
     * @param options1 the first set of options
     * @param options2 the second set of options
     * @throws Exception if the two sets of options differ
     */
    void compareOptions(String[] options1, String[] options2);

    /**
     * creates a copy of the given options
     * 
     * @param options	the options to copy
     * @return		the copy
     */
    String[] getCopy(String[] options);
  
    /**
     * returns a new instance of the OptionHandler's class
     * 
     * @return		a new instance
     */
    OptionHandler getDefaultHandler();

    /**
     * returns the default options the default OptionHandler will return
     * 
     * @return		the default options
     */
    String[] getDefaultOptions();
  
public:
    /**
     * checks whether the listOptions method works
     * 
     * @return index 0 is true if the test was passed, index 1 is always false
     */
    bool checkListOptions();
  
    /**
     * checks whether the user-supplied options can be processed at all
     * 
     * @return index 0 is true if the test was passed, index 1 is always false
     */
    bool checkSetOptions();
  
    /**
     * checks whether the default options can be processed completely
     * or some invalid options are returned by the getOptions() method.
     * 
     * @return index 0 is true if the test was passed, index 1 is always false
     */
    bool checkDefaultOptions();
  
    /**
     * checks whether the user-supplied options can be processed completely
     * or some "left-over" options remain
     * 
     * @return index 0 is true if the test was passed, index 1 is always false
     */
    bool checkRemainingOptions();
  
    /**
     * checks whether the user-supplied options stay the same after settting,
     * getting and re-setting again
     * 
     * @return index 0 is true if the test was passed, index 1 is always false
     */
    bool checkCanonicalUserOptions();
    /** 
     * Main method for using the CheckOptionHandler.
     *
     * @param args 	the options to the CheckOptionHandler
     */
    static void main(String[] args); 

};

#endif
