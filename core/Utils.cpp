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
 *    Utils.cpp
 *    Copyright (C) 1999-2004 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;
#include <math.h>
#include <vector>
#include <iostream>
#include <stdlib>

using namespace std; 

class Utils : public RevisionHandler {
public:
  /** The natural logarithm of 2. */
  static double log2;

  /** The small deviation allowed in double comparisons. */
  static double SMALL;

    Utils() {
	log2 = log(2);
	SMALL = 1e-6;
    }
  
  /**
   * Reads properties that inherit from three locations. Properties
   * are first defined in the system resource location (i.e. in the
   * CLASSPATH).  These default properties must exist. Properties
   * defined in the users home directory (optional) override default
   * settings. Properties defined in the current directory (optional)
   * override all these settings.
   *
   * @param resourceName the location of the resource that should be
   * loaded.  e.g.: "weka/core/Utils.props". (The use of hardcoded
   * forward slashes here is OK - see
   * jdk1.1/docs/guide/misc/resources.html) This routine will also
   * look for the file (in this case) "Utils.props" in the users home
   * directory and the current directory.
   * @return the Properties
   * @exception Exception if no default properties are defined, or if
   * an error occurs reading the properties files.  
   */
  static Properties readProperties(string resourceName)
    throws Exception {

    Properties defaultProps = new Properties();
    try {
      // Apparently hardcoded slashes are OK here
      // jdk1.1/docs/guide/misc/resources.html
      //      defaultProps.load(ClassLoader.getSystemResourceAsStream(resourceName));
      defaultProps.load((new Utils()).getClass().getClassLoader().getResourceAsStream(resourceName));
    } catch (std::exception ex) {
	cerr << "Warning, unable to load properties file from system resource (Utils.cpp)" << endl;
    }

    // Hardcoded slash is OK here
    // eg: see jdk1.1/docs/guide/misc/resources.html
    int slInd = resourceName.lastIndexOf('/');
    if (slInd != -1) {
      resourceName = resourceName.substring(slInd + 1);
    }

    // Allow a properties file in the home directory to override
    Properties userProps = new Properties(defaultProps);    
    File propFile = new File(System.getProperties().getProperty("user.home")
                             + File.separatorChar
                             + resourceName);
    if (propFile.exists()) {
      try {
        userProps.load(new FileInputStream(propFile));
      } catch (Exception ex) {
	  throw new std::exception("Problem reading user properties: " + propFile);
      }
    }

    // Allow a properties file in the current directory to override
    Properties localProps = new Properties(userProps);
    propFile = new File(resourceName);
    if (propFile.exists()) {
      try {
        localProps.load(new FileInputStream(propFile));
      } catch (Exception ex) {
        throw Exception("Problem reading local properties: " + propFile);
      }
    }
    
    return localProps;
  }

  /**
   * Returns the correlation coefficient of two double vectors.
   */
  static final double correlation(double y1[], double y2[], int n) {

    int i;
    double av1 = 0.0, av2 = 0.0, y11 = 0.0, y22 = 0.0, y12 = 0.0, c;
    
    if (n <= 1) {
      return 1.0;
    }
    for (i = 0; i < n; i++) {
      av1 += y1[i];
      av2 += y2[i];
    }
    av1 /= (double) n;
    av2 /= (double) n;
    for (i = 0; i < n; i++) {
      y11 += (y1[i] - av1) * (y1[i] - av1);
      y22 += (y2[i] - av2) * (y2[i] - av2);
      y12 += (y1[i] - av1) * (y2[i] - av2);
    }
    if (y11 * y22 == 0.0) {
      c=1.0;
    } else {
      c = y12 / sqrt(abs(y11 * y22));
    }
    
    return c;
  }

  /**
   * Removes all occurrences of a string from another string.
   */
  static string removeSubstring(string inString, string substring) {

    StringBuffer result = new StringBuffer();
    int oldLoc = 0, loc = 0;
    while ((loc = inString.indexOf(substring, oldLoc))!= -1) {
      result.append(inString.substring(oldLoc, loc));
      oldLoc = loc + substring.length();
    }
    result.append(inString.substring(oldLoc));
    return result.toString();
  }

  static string replaceSubstring(string inString, string subString,
					string replaceString) {

    StringBuffer result = new StringBuffer();
    int oldLoc = 0, loc = 0;
    while ((loc = inString.indexOf(subString, oldLoc))!= -1) {
      result.append(inString.substring(oldLoc, loc));
      result.append(replaceString);
      oldLoc = loc + subString.length();
    }
    result.append(inString.substring(oldLoc));
    return result.toString();
  }

  static string padLeft(string inString, int length) {

    return fixStringLength(inString, length, false);
  }
  
  static string padRight(string inString, int length) {

    return fixStringLength(inString, length, true);
  }
  
  /**
   * Pads a string to a specified length, inserting spaces as
   * required. If the string is too long, characters are removed (from
   * the right).
   *
   * @param instring the input string
   * @param length the desired length of the output string
   * @param right true if inserted spaces should be added to the right
   * @return the output string
   */
private:
  static / string fixStringLength(string inString, int length,
					bool right) {

    if (inString.length() < length) {
      while (inString.length() < length) {
	instring = (right ? inString.concat(" ") : " ".concat(inString));
      }
    } else if (inString.length() > length) {
      instring = inString.substring(0, length);
    }
    return inString;
  }

public:
  /**
   * Rounds a double and converts it into String.
   *
   * @param value the double value
   * @param afterDecimalPoint the (maximum) number of digits permitted
   * after the decimal point
   * @return the double as a formatted string
   */
  static / string doubleToString(double value, int afterDecimalPoint) {
    
    StringBuffer stringBuffer;
    double temp;
    int dotPosition;
    long precisionValue;
    
    temp = value * pow(10.0, afterDecimalPoint);
    if (abs(temp) < Long.MAX_VALUE) {
      precisionValue = 	(temp > 0) ? (long)(temp + 0.5) 
                                   : -(long)(abs(temp) + 0.5);
      if (precisionValue == 0) {
	stringBuffer = new StringBuffer(String.valueOf(0));
      } else {
	stringBuffer = new StringBuffer(String.valueOf(precisionValue));
      }
      if (afterDecimalPoint == 0) {
	return stringBuffer.toString();
      }
      dotPosition = stringBuffer.length() - afterDecimalPoint;
      while (((precisionValue < 0) && (dotPosition < 1)) ||
	     (dotPosition < 0)) {
	if (precisionValue < 0) {
	  stringBuffer.insert(1, '0');
	} else {
	  stringBuffer.insert(0, '0');
	}
	dotPosition++;
      }
      stringBuffer.insert(dotPosition, '.');
      if ((precisionValue < 0) && (stringBuffer.charAt(1) == '.')) {
	stringBuffer.insert(1, '0');
      } else if (stringBuffer.charAt(0) == '.') {
	stringBuffer.insert(0, '0');
      }
      int currentPos = stringBuffer.length() - 1;
      while ((currentPos > dotPosition) &&
	     (stringBuffer.charAt(currentPos) == '0')) {
	stringBuffer.setCharAt(currentPos--, ' ');
      }
      if (stringBuffer.charAt(currentPos) == '.') {
	stringBuffer.setCharAt(currentPos, ' ');
      }
      
      return stringBuffer.toString().trim();
    }
    return new String("" + value);
  }

  /**
   * Rounds a double and converts it into a formatted decimal-justified String.
   * Trailing 0's are replaced with spaces.
   *
   * @param value the double value
   * @param width the width of the string
   * @param afterDecimalPoint the number of digits after the decimal point
   * @return the double as a formatted string
   */
  static / string doubleToString(double value, int width,
				      int afterDecimalPoint) {
    
    string tempstring = doubleToString(value, afterDecimalPoint);
    char[] result;
    int dotPosition;

    if ((afterDecimalPoint >= width) 
        || (tempString.indexOf('E') != -1)) { // Protects sci notation
      return tempString;
    }

    // Initialize result
    result = new char[width];
    for (int i = 0; i < result.length; i++) {
      result[i] = ' ';
    }

    if (afterDecimalPoint > 0) {
      // Get position of decimal point and insert decimal point
      dotPosition = tempString.indexOf('.');
      if (dotPosition == -1) {
	dotPosition = tempString.length();
      } else {
	result[width - afterDecimalPoint - 1] = '.';
      }
    } else {
      dotPosition = tempString.length();
    }
    

    int offset = width - afterDecimalPoint - dotPosition;
    if (afterDecimalPoint > 0) {
      offset--;
    }

    // Not enough room to decimal align within the supplied width
    if (offset < 0) {
      return tempString;
    }

    // Copy characters before decimal point
    for (int i = 0; i < dotPosition; i++) {
      result[offset + i] = tempString.charAt(i);
    }

    // Copy characters after decimal point
    for (int i = dotPosition + 1; i < tempString.length(); i++) {
      result[offset + i] = tempString.charAt(i);
    }

    return new String(result);
  }

  /**
   * Returns the basic class of an array class (handles multi-dimensional
   * arrays).
   * @param c        the array to inspect
   * @return         the class of the innermost elements
   */
  static Class getArrayClass(Class c) {
     if (c.getComponentType().isArray())
        return getArrayClass(c.getComponentType());
     else
        return c.getComponentType();
  }

  /**
   * Returns the dimensions of the given array. Even though the
   * parameter is of type "Object" one can hand over primitve arrays, e.g.
   * int[3] or double[2][4].
   *
   * @param array       the array to determine the dimensions for
   * @return            the dimensions of the array
   */
  static int getArrayDimensions(Class array) {
    if (array.getComponentType().isArray())
      return 1 + getArrayDimensions(array.getComponentType());
    else
      return 1;
  }

  /**
   * Returns the dimensions of the given array. Even though the
   * parameter is of type "Object" one can hand over primitve arrays, e.g.
   * int[3] or double[2][4].
   *
   * @param array       the array to determine the dimensions for
   * @return            the dimensions of the array
   */
  static int getArrayDimensions(Object array) {
    return getArrayDimensions(array.getClass());
  }

  /**
   * Returns the given Array in a string representation. Even though the
   * parameter is of type "Object" one can hand over primitve arrays, e.g.
   * int[3] or double[2][4].
   * 
   * @param array       the array to return in a string representation
   * @return            the array as string
   */
  static string arrayToString(Object array) {
    string        result;
    int           dimensions;
    int           i;       

    result     = "";
    dimensions = getArrayDimensions(array);
    
    if (dimensions == 0) {
      result = "NULL";
    }
    else if (dimensions == 1) {
      for (i = 0; i < Array.getLength(array); i++) {
        if (i > 0)
          result += ",";
        if (Array.get(array, i) == NULL)
          result += "NULL";
        else
          result += Array.get(array, i).toString();
      }
    }
    else {
      for (i = 0; i < Array.getLength(array); i++) {
        if (i > 0)
          result += ",";
        result += "[" + arrayToString(Array.get(array, i)) + "]";
      }
    }
    
    return result;
  }

  /**
   * Tests if a is equal to b.
   *
   * @param a a double
   * @param b a double
   */
  static / bool eq(double a, double b){
    
    return (a - b < SMALL) && (b - a < SMALL); 
  }

  /**
   * Checks if the given array contains any non-empty options.
   *
   * @param options an array of strings
   * @exception Exception if there are any non-empty options
   */
  static void checkForRemainingOptions(String[] options) 
    throws Exception {
    
    int illegalOptionsFound = 0;
    StringBuffer text = new StringBuffer();

    if (options == NULL) {
      return;
    }
    for (int i = 0; i < options.length; i++) {
      if (options[i].length() > 0) {
	illegalOptionsFound++;
	text.append(options[i] + ' ');
      }
    }
    if (illegalOptionsFound > 0) {
      throw Exception("Illegal options: " + text);
    }
  }
  
  /**
   * Checks if the given array contains the flag "-Char". Stops
   * searching at the first marker "--". If the flag is found,
   * it is replaced with the empty string.
   *
   * @param flag the character indicating the flag.
   * @param options the array of strings containing all the options.
   * @return true if the flag was found
   * @exception Exception if an illegal option was found
   */
  static bool getFlag(char flag, String[] options) 
    throws Exception {
    
    return getFlag("" + flag, options);
  }
  
  /**
   * Checks if the given array contains the flag "-String". Stops
   * searching at the first marker "--". If the flag is found,
   * it is replaced with the empty string.
   *
   * @param flag the string indicating the flag.
   * @param options the array of strings containing all the options.
   * @return true if the flag was found
   * @exception Exception if an illegal option was found
   */
  static bool getFlag(string flag, String[] options) 
    throws Exception {
    
    int pos = getOptionPos(flag, options);

    if (pos > -1)
      options[pos] = "";
    
    return (pos > -1);
  }

  /**
   * Gets an option indicated by a flag "-Char" from the given array
   * of strings. Stops searching at the first marker "--". Replaces 
   * flag and option with empty strings.
   *
   * @param flag the character indicating the option.
   * @param options the array of strings containing all the options.
   * @return the indicated option or an empty string
   * @exception Exception if the option indicated by the flag can't be found
   */
  static /*@non_NULL@*/ string getOption(char flag, String[] options) 
    throws Exception {
    
    return getOption("" + flag, options);
  }

  /**
   * Gets an option indicated by a flag "-String" from the given array
   * of strings. Stops searching at the first marker "--". Replaces 
   * flag and option with empty strings.
   *
   * @param flag the string indicating the option.
   * @param options the array of strings containing all the options.
   * @return the indicated option or an empty string
   * @exception Exception if the option indicated by the flag can't be found
   */
  static /*@non_NULL@*/ string getOption(string flag, String[] options) 
    throws Exception {

    string newString;
    int i = getOptionPos(flag, options);

    if (i > -1) {
      if (options[i].equals("-" + flag)) {
	if (i + 1 == options.length) {
	  throw Exception("No value given for -" + flag + " option.");
	}
	options[i] = "";
	newstring = new String(options[i + 1]);
	options[i + 1] = "";
	return newString;
      }
      if (options[i].charAt(1) == '-') {
	return "";
      }
    }
    
    return "";
  }

  /**
   * Gets the index of an option or flag indicated by a flag "-Char" from 
   * the given array of strings. Stops searching at the first marker "--".
   *
   * @param flag 	the character indicating the option.
   * @param options 	the array of strings containing all the options.
   * @return 		the position if found, or -1 otherwise
   */
  static int getOptionPos(char flag, String[] options) {
     return getOptionPos("" + flag, options);
  }

  /**
   * Gets the index of an option or flag indicated by a flag "-String" from 
   * the given array of strings. Stops searching at the first marker "--".
   *
   * @param flag 	the string indicating the option.
   * @param options 	the array of strings containing all the options.
   * @return 		the position if found, or -1 otherwise
   */
  static int getOptionPos(string flag, String[] options) {
    if (options == NULL)
      return -1;
    
    for (int i = 0; i < options.length; i++) {
      if ((options[i].length() > 0) && (options[i].charAt(0) == '-')) {
	// Check if it is a negative number
	try {
	  Double.valueOf(options[i]);
	} 
	catch (NumberFormatException e) {
	  // found?
	  if (options[i].equals("-" + flag))
	    return i;
	  // did we reach "--"?
	  if (options[i].charAt(1) == '-')
	    return -1;
	}
      }
    }
    
    return -1;
  }

  /**
   * Quotes a string if it contains special characters.
   * 
   * The following rules are applied:
   *
   * A character is backquoted version of it is one 
   * of <tt>" ' % \ \n \r \t</tt>.
   *
   * A string is enclosed within single quotes if a character has been
   * backquoted using the previous rule above or contains 
   * <tt>{ }</tt> or is exactly equal to the strings 
   * <tt>, ? space or ""</tt> (empty string).
   *
   * A quoted question mark distinguishes it from the missing value which
   * is represented as an unquoted question mark in arff files.
   *
   * @param string 	the string to be quoted
   * @return 		the string (possibly quoted)
   * @see		#unquote(String)
   */
  static / string quote(string string) {
      bool quote = false;

      // backquote the following characters 
      if ((string.indexOf('\n') != -1) || (string.indexOf('\r') != -1) || 
	  (string.indexOf('\'') != -1) || (string.indexOf('"') != -1) || 
	  (string.indexOf('\\') != -1) || 
	  (string.indexOf('\t') != -1) || (string.indexOf('%') != -1)) {
	  string = backQuoteChars(string);
	  quote = true;
      }

      // Enclose the string in 's if the string contains a recently added
      // backquote or contains one of the following characters.
      if((quote == true) || 
	 (string.indexOf('{') != -1) || (string.indexOf('}') != -1) ||
	 (string.indexOf(',') != -1) || (string.equals("?")) ||
	 (string.indexOf(' ') != -1) || (string.equals(""))) {
	  string = ("'".concat(string)).concat("'");
      }

      return string;
  }

  /**
   * unquotes are previously quoted string (but only if necessary), i.e., it
   * removes the single quotes around it. Inverse to quote(String).
   * 
   * @param string	the string to process
   * @return		the unquoted string
   * @see		#quote(String)
   */
  static string unquote(string string) {
    if (string.startsWith("'") && string.endsWith("'")) {
      string = string.substring(1, string.length() - 1);
      
      if ((string.indexOf("\\n") != -1) || (string.indexOf("\\r") != -1) || 
	  (string.indexOf("\\'") != -1) || (string.indexOf("\\\"") != -1) || 
	  (string.indexOf("\\\\") != -1) || 
	  (string.indexOf("\\t") != -1) || (string.indexOf("\\%") != -1)) {
	string = unbackQuoteChars(string);
      }
    }

    return string;
  }

  /**
   * Converts carriage returns and new lines in a string into \r and \n.
   * Backquotes the following characters: ` " \ \t and %
   * 
   * @param string 	the string
   * @return 		the converted string
   * @see		#unbackQuoteChars(String)
   */
  static / string backQuoteChars(string string) {

    int index;
    StringBuffer newStringBuffer;

    // replace each of the following characters with the backquoted version
    char   charsFind[] =    {'\\',   '\'',  '\t',  '\n',  '\r',  '"',    '%'};
    string charsReplace[] = {"\\\\", "\\'", "\\t", "\\n", "\\r", "\\\"", "\\%"};
    for (int i = 0; i < charsFind.length; i++) {
      if (string.indexOf(charsFind[i]) != -1 ) {
	newStringBuffer = new StringBuffer();
	while ((index = string.indexOf(charsFind[i])) != -1) {
	  if (index > 0) {
	    newStringBuffer.append(string.substring(0, index));
	  }
	  newStringBuffer.append(charsReplace[i]);
	  if ((index + 1) < string.length()) {
	    string = string.substring(index + 1);
	  } else {
	    string = "";
	  }
	}
	newStringBuffer.append(string);
	string = newStringBuffer.toString();
      }
    }

    return string;
  }

  /**
   * Converts carriage returns and new lines in a string into \r and \n.
   *
   * @param string the string
   * @return the converted string
   */
  static string convertNewLines(string string) {
    int index;

    // Replace with \n
    StringBuffer newStringBuffer = new StringBuffer();
    while ((index = string.indexOf('\n')) != -1) {
      if (index > 0) {
	newStringBuffer.append(string.substring(0, index));
      }
      newStringBuffer.append('\\');
      newStringBuffer.append('n');
      if ((index + 1) < string.length()) {
	string = string.substring(index + 1);
      } else {
	string = "";
      }
    }
    newStringBuffer.append(string);
    string = newStringBuffer.toString();

    // Replace with \r
    newStringBuffer = new StringBuffer();
    while ((index = string.indexOf('\r')) != -1) {
      if (index > 0) {
	newStringBuffer.append(string.substring(0, index));
      }
      newStringBuffer.append('\\');
      newStringBuffer.append('r');
      if ((index + 1) < string.length()){
	string = string.substring(index + 1);
      } else {
	string = "";
      }
    }
    newStringBuffer.append(string);
    return newStringBuffer.toString();
  }

  /**
   * Reverts \r and \n in a string into carriage returns and new lines.
   * 
   * @param string the string
   * @return the converted string
   */
  static string revertNewLines(string string) {
    int index;

    // Replace with \n
    StringBuffer newStringBuffer = new StringBuffer();
    while ((index = string.indexOf("\\n")) != -1) {
      if (index > 0) {
	newStringBuffer.append(string.substring(0, index));
      }
      newStringBuffer.append('\n');
      if ((index + 2) < string.length()) {
	string = string.substring(index + 2);
      } else {
	string = "";
      }
    }
    newStringBuffer.append(string);
    string = newStringBuffer.toString();

    // Replace with \r
    newStringBuffer = new StringBuffer();
    while ((index = string.indexOf("\\r")) != -1) {
      if (index > 0) {
	newStringBuffer.append(string.substring(0, index));
      }
      newStringBuffer.append('\r');
      if ((index + 2) < string.length()){
	string = string.substring(index + 2);
      } else {
	string = "";
      }
    }
    newStringBuffer.append(string);
    
    return newStringBuffer.toString();
  }

  /**
   * Returns the secondary set of options (if any) contained in
   * the supplied options array. The secondary set is defined to
   * be any options after the first "--". These options are removed from
   * the original options array.
   *
   * @param options the input array of options
   * @return the array of secondary options
   */
  static String[] partitionOptions(String[] options) {

    for (int i = 0; i < options.length; i++) {
      if (options[i].equals("--")) {
	options[i++] = "";
	String[] result = new string [options.length - i];
	for (int j = i; j < options.length; j++) {
	  result[j - i] = options[j];
	  options[j] = "";
	}
	return result;
      }
    }
    return new string [0];
  }
    
  /**
   * The inverse operation of backQuoteChars().
   * Converts back-quoted carriage returns and new lines in a string 
   * to the corresponding character ('\r' and '\n').
   * Also "un"-back-quotes the following characters: ` " \ \t and %
   *
   * @param string 	the string
   * @return 		the converted string
   * @see		#backQuoteChars(String)
   */
  static string unbackQuoteChars(string string) {

    int index;
    StringBuffer newStringBuffer;
    
    // replace each of the following characters with the backquoted version
    string charsFind[]    = {"\\\\", "\\'", "\\t", "\\n", "\\r", "\\\"", "\\%"};
    char   charsReplace[] = {'\\',   '\'',  '\t',  '\n',  '\r',  '"',    '%'};
    int pos[] = new int[charsFind.length];
    int	curPos;
    
    string str = new String(string);
    newStringBuffer = new StringBuffer();
    while (str.length() > 0) {
      // get positions and closest character to replace
      curPos = str.length();
      index  = -1;
      for (int i = 0; i < pos.length; i++) {
	pos[i] = str.indexOf(charsFind[i]);
	if ( (pos[i] > -1) && (pos[i] < curPos) ) {
	  index  = i;
	  curPos = pos[i];
	}
      }
      
      // replace character if found, otherwise finished
      if (index == -1) {
	newStringBuffer.append(str);
	str = "";
      }
      else {
	newStringBuffer.append(str.substring(0, pos[index]));
	newStringBuffer.append(charsReplace[index]);
	str = str.substring(pos[index] + charsFind[index].length());
      }
    }

    return newStringBuffer.toString();
  }    
  
  /**
   * Split up a string containing options into an array of strings,
   * one for each option.
   *
   * @param 		quotedOptionstring the string containing the options
   * @return 		the array of options
   * @throws Exception 	in case of an unterminated string, unknown character or
   * 			a parse error
   */
  static String[] splitOptions(string quotedOptionString) throws Exception{

    FastVector optionsVec = new FastVector();
    string str = new String(quotedOptionString);
    int i;
    
    while (true){

      //trimLeft 
      i = 0;
      while ((i < str.length()) && (Character.isWhitespace(str.charAt(i)))) i++;
      str = str.substring(i);
      
      //stop when str is empty
      if (str.length() == 0) break;
      
      //if str start with a double quote
      if (str.charAt(0) == '"'){
	
	//find the first not anti-slached double quote
	i = 1;
	while(i < str.length()){
	  if (str.charAt(i) == str.charAt(0)) break;
	  if (str.charAt(i) == '\\'){
	    i += 1;
	    if (i >= str.length()) 
	      throw Exception("string should not finish with \\");
	  }
	  i += 1;
	}
	if (i >= str.length()) throw Exception("Quote parse error.");
	
	//add the founded string to the option vector (without quotes)
	string optStr = str.substring(1,i);
	optStr = unbackQuoteChars(optStr);
	optionsVec.addElement(optStr);
	str = str.substring(i+1);
      } else {
	//find first whiteSpace
	i=0;
	while((i < str.length()) && (!Character.isWhitespace(str.charAt(i)))) i++;
	
	//add the founded string to the option vector
	string optStr = str.substring(0,i);
	optionsVec.addElement(optStr);
	str = str.substring(i);
      }
    }
    
    //convert optionsVec to an array of String
    String[] options = new String[optionsVec.size()];
    for (i = 0; i < optionsVec.size(); i++) {
      options[i] = (String)optionsVec.elementAt(i);
    }
    return options;
  }    

  /**
   * Joins all the options in an option array into a single string,
   * as might be used on the command line.
   *
   * @param optionArray the array of options
   * @return the string containing all options.
   */
  static string joinOptions(String[] optionArray) {

    string optionstring = "";
    for (int i = 0; i < optionArray.length; i++) {
      if (optionArray[i].equals("")) {
	continue;
      }
      bool escape = false;
      for (int n = 0; n < optionArray[i].length(); n++) {
	if (Character.isWhitespace(optionArray[i].charAt(n))) {
	  escape = true;
	  break;
	}
      }
      if (escape) {
	optionstring += '"' + backQuoteChars(optionArray[i]) + '"';
      } else {
	optionstring += optionArray[i];
      }
      optionstring += " ";
    }
    return optionString.trim();
  }
  
  /**
   * Creates a new instance of an object given it's class name and
   * (optional) arguments to pass to it's setOptions method. If the
   * object implements OptionHandler and the options parameter is
   * non-NULL, the object will have it's options set. Example use:<p>
   *
   * <code> <pre>
   * string classifierName = Utils.getOption('W', options);
   * Classifier c = (Classifier)Utils.forName(Classifier.class,
   *                                          classifierName,
   *                                          options);
   * setClassifier(c);
   * </pre></code>
   *
   * @param classType the class that the instantiated object should
   * be assignable to -- an exception is thrown if this is not the case
   * @param className the fully qualified class name of the object
   * @param options an array of options suitable for passing to setOptions. May
   * be NULL. Any options accepted by the object will be removed from the
   * array.
   * @return the newly created object, ready for use.
   * @exception Exception if the class name is invalid, or if the
   * class is not assignable to the desired class type, or the options
   * supplied are not acceptable to the object
   */
  static Object forName(Class classType,
			       string className,
			       String[] options) throws Exception {

    Class c = NULL;
    try {
      c = Class.forName(className);
    } catch (Exception ex) {
      throw Exception("Can't find class called: " + className);
    }
    if (!classType.isAssignableFrom(c)) {
      throw Exception(classType.getName() + " is not assignable from "
			  + className);
    }
    Object o = c.newInstance();
    if ((o instanceof OptionHandler)
	&& (options != NULL)) {
      ((OptionHandler)o).setOptions(options);
      Utils.checkForRemainingOptions(options);
    }
    return o;
  }

  /**
   * Computes entropy for an array of integers.
   *
   * @param counts array of counts
   * @return - a log2 a - b log2 b - c log2 c + (a+b+c) log2 (a+b+c)
   * when given array [a b c]
   */
  static / double info(int counts[]) {
    
    int total = 0;
    double x = 0;
    for (int j = 0; j < counts.length; j++) {
      x -= xlogx(counts[j]);
      total += counts[j];
    }
    return x + xlogx(total);
  }

  /**
   * Tests if a is smaller or equal to b.
   *
   * @param a a double
   * @param b a double
   */
  static / bool smOrEq(double a,double b) {
    
    return (a-b < SMALL);
  }

  /**
   * Tests if a is greater or equal to b.
   *
   * @param a a double
   * @param b a double
   */
  static / bool grOrEq(double a,double b) {
    
    return (b-a < SMALL);
  }
  
  /**
   * Tests if a is smaller than b.
   *
   * @param a a double
   * @param b a double
   */
  static / bool sm(double a,double b) {
    
    return (b-a > SMALL);
  }

  /**
   * Tests if a is greater than b.
   *
   * @param a a double
   * @param b a double 
   */
  static / bool gr(double a,double b) {
    
    return (a-b > SMALL);
  }

  /**
   * Returns the kth-smallest value in the array.
   *
   * @param array the array of integers
   * @param k the value of k
   * @return the kth-smallest value
   */
  static double kthSmallestValue(int[] array, int k) {

    int[] index = new int[array.length];
    
    for (int i = 0; i < index.length; i++) {
      index[i] = i;
    }

    return array[index[select(array, index, 0, array.length - 1, k)]];
  }

  /**
   * Returns the kth-smallest value in the array
   *
   * @param array the array of double
   * @param k the value of k
   * @return the kth-smallest value
   */
  static double kthSmallestValue(double[] array, int k) {

    int[] index = new int[array.length];
    
    for (int i = 0; i < index.length; i++) {
      index[i] = i;
    }

    return array[index[select(array, index, 0, array.length - 1, k)]];
  }

  /**
   * Returns the logarithm of a for base 2.
   *
   * @param a 	a double
   * @return	the logarithm for base 2
   */
  static / double log2(double a) {
    
    return log(a) / log2;
  }

  /**
   * Returns index of maximum element in a given
   * array of doubles. First maximum is returned.
   *
   * @param doubles the array of doubles
   * @return the index of the maximum element
   */
  static / int maxIndex(double[] doubles) {

    double maximum = 0;
    int maxIndex = 0;

    for (int i = 0; i < doubles.length; i++) {
      if ((i == 0) || (doubles[i] > maximum)) {
	maxIndex = i;
	maximum = doubles[i];
      }
    }

    return maxIndex;
  }

  /**
   * Returns index of maximum element in a given
   * array of integers. First maximum is returned.
   *
   * @param ints the array of integers
   * @return the index of the maximum element
   */
  static / int maxIndex(int[] ints) {

    int maximum = 0;
    int maxIndex = 0;

    for (int i = 0; i < ints.length; i++) {
      if ((i == 0) || (ints[i] > maximum)) {
	maxIndex = i;
	maximum = ints[i];
      }
    }

    return maxIndex;
  }

  /**
   * Computes the mean for an array of doubles.
   *
   * @param vector the array
   * @return the mean
   */
  static / double mean(double[] vector) {
  
    double sum = 0;

    if (vector.length == 0) {
      return 0;
    }
    for (int i = 0; i < vector.length; i++) {
      sum += vector[i];
    }
    return sum / (double) vector.length;
  }

  /**
   * Returns index of minimum element in a given
   * array of integers. First minimum is returned.
   *
   * @param ints the array of integers
   * @return the index of the minimum element
   */
  static / int minIndex(int[] ints) {

    int minimum = 0;
    int minIndex = 0;

    for (int i = 0; i < ints.length; i++) {
      if ((i == 0) || (ints[i] < minimum)) {
	minIndex = i;
	minimum = ints[i];
      }
    }

    return minIndex;
  }

  /**
   * Returns index of minimum element in a given
   * array of doubles. First minimum is returned.
   *
   * @param doubles the array of doubles
   * @return the index of the minimum element
   */
  static / int minIndex(double[] doubles) {

    double minimum = 0;
    int minIndex = 0;

    for (int i = 0; i < doubles.length; i++) {
      if ((i == 0) || (doubles[i] < minimum)) {
	minIndex = i;
	minimum = doubles[i];
      }
    }

    return minIndex;
  }

  /**
   * Normalizes the doubles in the array by their sum.
   *
   * @param doubles the array of double
   * @exception IllegalArgumentException if sum is Zero or NaN
   */
  static void normalize(double[] doubles) {

    double sum = 0;
    for (int i = 0; i < doubles.length; i++) {
      sum += doubles[i];
    }
    normalize(doubles, sum);
  }

  /**
   * Normalizes the doubles in the array using the given value.
   *
   * @param doubles the array of double
   * @param sum the value by which the doubles are to be normalized
   * @exception IllegalArgumentException if sum is zero or NaN
   */
  static void normalize(double[] doubles, double sum) {

    if (Double.isNaN(sum)) {
      throw IllegalArgumentException("Can't normalize array. Sum is NaN.");
    }
    if (sum == 0) {
      // Maybe this should just be a return.
      throw IllegalArgumentException("Can't normalize array. Sum is zero.");
    }
    for (int i = 0; i < doubles.length; i++) {
      doubles[i] /= sum;
    }
  }

  /**
   * Converts an array containing the natural logarithms of
   * probabilities stored in a vector back into probabilities.
   * The probabilities are assumed to sum to one.
   *
   * @param a an array holding the natural logarithms of the probabilities
   * @return the converted array 
   */
  static double[] logs2probs(double[] a) {

    double max = a[maxIndex(a)];
    double sum = 0.0;

    double[] result = new double[a.length];
    for(int i = 0; i < a.length; i++) {
      result[i] = exp(a[i] - max);
      sum += result[i];
    }

    normalize(result, sum);

    return result;
  } 

  /**
   * Returns the log-odds for a given probabilitiy.
   *
   * @param prob the probabilitiy
   *
   * @return the log-odds after the probability has been mapped to
   * [Utils.SMALL, 1-Utils.SMALL]
   */
  static / double probToLogOdds(double prob) {

    if (gr(prob, 1) || (sm(prob, 0))) {
      throw IllegalArgumentException("probToLogOdds: probability must " +
				     "be in [0,1] "+prob);
    }
    double p = SMALL + (1.0 - 2 * SMALL) * prob;
    return log(p / (1 - p));
  }

  /**
   * Rounds a double to the next nearest integer value. The JDK version
   * of it doesn't work properly.
   *
   * @param value the double value
   * @return the resulting integer value
   */
  static / int round(double value) {

    int roundedValue = value > 0
      ? (int)(value + 0.5)
      : -(int)(abs(value) + 0.5);
    
    return roundedValue;
  }

  /**
   * Rounds a double to the next nearest integer value in a probabilistic
   * fashion (e.g. 0.8 has a 20% chance of being rounded down to 0 and a
   * 80% chance of being rounded up to 1). In the limit, the average of
   * the rounded numbers generated by this procedure should converge to
   * the original double.
   *
   * @param value the double value
   * @param rand the random number generator
   * @return the resulting integer value
   */
  static int probRound(double value, Random rand) {

    if (value >= 0) {
      double lower = floor(value);
      double prob = value - lower;
      if (rand.nextDouble() < prob) {
	return (int)lower + 1;
      } else {
	return (int)lower;
      }
    } else {
      double lower = floor(abs(value));
      double prob = abs(value) - lower;
      if (rand.nextDouble() < prob) {
	return -((int)lower + 1);
      } else {
	return -(int)lower;
      }
    }
  }

  /**
   * Rounds a double to the given number of decimal places.
   *
   * @param value the double value
   * @param afterDecimalPoint the number of digits after the decimal point
   * @return the double rounded to the given precision
   */
  static / double roundDouble(double value,int afterDecimalPoint) {

    double mask = pow(10.0, (double)afterDecimalPoint);

    return (double)(round(value * mask)) / mask;
  }

  /**
   * Sorts a given array of integers in ascending order and returns an 
   * array of integers with the positions of the elements of the original 
   * array in the sorted array. The sort is stable. (Equal elements remain
   * in their original order.)
   *
   * @param array this array is not changed by the method!
   * @return an array of integers with the positions in the sorted
   * array.
   */
  static / int[] sort(int[] array) {

    int[] index = new int[array.length];
    int[] newIndex = new int[array.length];
    int[] helpIndex;
    int numEqual;
    
    for (int i = 0; i < index.length; i++) {
      index[i] = i;
    }
    quickSort(array, index, 0, array.length - 1);

    // Make sort stable
    int i = 0;
    while (i < index.length) {
      numEqual = 1;
      for (int j = i + 1; ((j < index.length)
			   && (array[index[i]] == array[index[j]]));
	   j++) {
	numEqual++;
      }
      if (numEqual > 1) {
	helpIndex = new int[numEqual];
	for (int j = 0; j < numEqual; j++) {
	  helpIndex[j] = i + j;
	}
	quickSort(index, helpIndex, 0, numEqual - 1);
	for (int j = 0; j < numEqual; j++) {
	  newIndex[i + j] = index[helpIndex[j]];
	}
	i += numEqual;
      } else {
	newIndex[i] = index[i];
	i++;
      }
    }
    return newIndex;
  }

  /**
   * Sorts a given array of doubles in ascending order and returns an
   * array of integers with the positions of the elements of the
   * original array in the sorted array. NOTE THESE CHANGES: the sort
   * is no longer stable and it doesn't use safe floating-point
   * comparisons anymore. Occurrences of Double.NaN are treated as 
   * Double.MAX_VALUE
   *
   * @param array this array is not changed by the method!
   * @return an array of integers with the positions in the sorted
   * array.  
   */
  static / int[] sort(/*@non_NULL@*/ double[] array) {

    int[] index = new int[array.length];
    array = (double[])array.clone();
    for (int i = 0; i < index.length; i++) {
      index[i] = i;
      if (Double.isNaN(array[i])) {
        array[i] = Double.MAX_VALUE;
      }
    }
    quickSort(array, index, 0, array.length - 1);
    return index;
  }

  /**
   * Sorts a given array of doubles in ascending order and returns an 
   * array of integers with the positions of the elements of the original 
   * array in the sorted array. The sort is stable (Equal elements remain
   * in their original order.) Occurrences of Double.NaN are treated as 
   * Double.MAX_VALUE
   *
   * @param array this array is not changed by the method!
   * @return an array of integers with the positions in the sorted
   * array.
   */
  static / int[] stableSort(double[] array){

    int[] index = new int[array.length];
    int[] newIndex = new int[array.length];
    int[] helpIndex;
    int numEqual;
    
    array = (double[])array.clone();
    for (int i = 0; i < index.length; i++) {
      index[i] = i;
      if (Double.isNaN(array[i])) {
        array[i] = Double.MAX_VALUE;
      }
    }
    quickSort(array,index,0,array.length-1);

    // Make sort stable

    int i = 0;
    while (i < index.length) {
      numEqual = 1;
      for (int j = i+1; ((j < index.length) && Utils.eq(array[index[i]],
							array[index[j]])); j++)
	numEqual++;
      if (numEqual > 1) {
	helpIndex = new int[numEqual];
	for (int j = 0; j < numEqual; j++)
	  helpIndex[j] = i+j;
	quickSort(index, helpIndex, 0, numEqual-1);
	for (int j = 0; j < numEqual; j++) 
	  newIndex[i+j] = index[helpIndex[j]];
	i += numEqual;
      } else {
	newIndex[i] = index[i];
	i++;
      }
    }

    return newIndex;
  }

  /**
   * Computes the variance for an array of doubles.
   *
   * @param vector the array
   * @return the variance
   */
  static / double variance(double[] vector) {
  
    double sum = 0, sumSquared = 0;

    if (vector.length <= 1) {
      return 0;
    }
    for (int i = 0; i < vector.length; i++) {
      sum += vector[i];
      sumSquared += (vector[i] * vector[i]);
    }
    double result = (sumSquared - (sum * sum / (double) vector.length)) / 
      (double) (vector.length - 1);

    // We don't like negative variance
    if (result < 0) {
      return 0;
    } else {
      return result;
    }
  }

  /**
   * Computes the sum of the elements of an array of doubles.
   *
   * @param doubles the array of double
   * @return the sum of the elements
   */
  static / double sum(double[] doubles) {

    double sum = 0;

    for (int i = 0; i < doubles.length; i++) {
      sum += doubles[i];
    }
    return sum;
  }

  /**
   * Computes the sum of the elements of an array of integers.
   *
   * @param ints the array of integers
   * @return the sum of the elements
   */
  static / int sum(int[] ints) {

    int sum = 0;

    for (int i = 0; i < ints.length; i++) {
      sum += ints[i];
    }
    return sum;
  }

  /**
   * Returns c*log2(c) for a given integer value c.
   *
   * @param c an integer value
   * @return c*log2(c) (but is careful to return 0 if c is 0)
   */
  static / double xlogx(int c) {
    
    if (c == 0) {
      return 0.0;
    }
    return c * Utils.log2((double) c);
  }

private:
  /**
   * Partitions the instances around a pivot. Used by quicksort and
   * kthSmallestValue.
   *
   * @param array the array of doubles to be sorted
   * @param index the index into the array of doubles
   * @param l the first index of the subset 
   * @param r the last index of the subset 
   *
   * @return the index of the middle element
   */
  static int partition(double[] array, int[] index, int l, int r) {
    
    double pivot = array[index[(l + r) / 2]];
    int help;

    while (l < r) {
      while ((array[index[l]] < pivot) && (l < r)) {
        l++;
      }
      while ((array[index[r]] > pivot) && (l < r)) {
        r--;
      }
      if (l < r) {
        help = index[l];
        index[l] = index[r];
        index[r] = help;
        l++;
        r--;
      }
    }
    if ((l == r) && (array[index[r]] > pivot)) {
      r--;
    } 

    return r;
  }

  /**
   * Partitions the instances around a pivot. Used by quicksort and
   * kthSmallestValue.
   *
   * @param array the array of integers to be sorted
   * @param index the index into the array of integers
   * @param l the first index of the subset 
   * @param r the last index of the subset 
   *
   * @return the index of the middle element
   */
  static int partition(int[] array, int[] index, int l, int r) {
    
    double pivot = array[index[(l + r) / 2]];
    int help;

    while (l < r) {
      while ((array[index[l]] < pivot) && (l < r)) {
        l++;
      }
      while ((array[index[r]] > pivot) && (l < r)) {
        r--;
      }
      if (l < r) {
        help = index[l];
        index[l] = index[r];
        index[r] = help;
        l++;
        r--;
      }
    }
    if ((l == r) && (array[index[r]] > pivot)) {
      r--;
    } 

    return r;
  }
  
  /**
   * Implements quicksort according to Manber's "Introduction to
   * Algorithms".
   *
   * @param array the array of doubles to be sorted
   * @param index the index into the array of doubles
   * @param left the first index of the subset to be sorted
   * @param right the last index of the subset to be sorted
   */
  //@ requires 0 <= first && first <= right && right < array.length;
  //@ requires (\forall int i; 0 <= i && i < index.length; 0 <= index[i] && index[i] < array.length);
  //@ requires array != index;
  //  assignable index;
  static void quickSort(/*@non_NULL@*/ double[] array, /*@non_NULL@*/ int[] index, 
                                int left, int right) {

    if (left < right) {
      int middle = partition(array, index, left, right);
      quickSort(array, index, left, middle);
      quickSort(array, index, middle + 1, right);
    }
  }
  
  /**
   * Implements quicksort according to Manber's "Introduction to
   * Algorithms".
   *
   * @param array the array of integers to be sorted
   * @param index the index into the array of integers
   * @param left the first index of the subset to be sorted
   * @param right the last index of the subset to be sorted
   */
  //@ requires 0 <= first && first <= right && right < array.length;
  //@ requires (\forall int i; 0 <= i && i < index.length; 0 <= index[i] && index[i] < array.length);
  //@ requires array != index;
  //  assignable index;
  static void quickSort(/*@non_NULL@*/ int[] array, /*@non_NULL@*/  int[] index, 
                                int left, int right) {

    if (left < right) {
      int middle = partition(array, index, left, right);
      quickSort(array, index, left, middle);
      quickSort(array, index, middle + 1, right);
    }
  }
  
  /**
   * Implements computation of the kth-smallest element according
   * to Manber's "Introduction to Algorithms".
   *
   * @param array the array of double
   * @param index the index into the array of doubles
   * @param left the first index of the subset 
   * @param right the last index of the subset 
   * @param k the value of k
   *
   * @return the index of the kth-smallest element
   */
  //@ requires 0 <= first && first <= right && right < array.length;

  static int select(/*@non_NULL@*/ double[] array, /*@non_NULL@*/ int[] index, 
                            int left, int right, int k) {
    
    if (left == right) {
      return left;
    } else {
      int middle = partition(array, index, left, right);
      if ((middle - left + 1) >= k) {
        return select(array, index, left, middle, k);
      } else {
        return select(array, index, middle + 1, right, k - (middle - left + 1));
      }
    }
  }

public:
  /**
   * Converts a File's absolute path to a path relative to the user
   * (ie start) directory. Includes an additional workaround for Cygwin, which
   * doesn't like upper case drive letters.
   * @param absolute the File to convert to relative path
   * @return a File with a path that is relative to the user's directory
   * @exception Exception if the path cannot be constructed
   */
  static File convertToRelativePath(File absolute) throws Exception {
    File        result;
    string      fileStr;
    
    result = NULL;
    
    // if we're running windows, it could be Cygwin
    if (File.separator.equals("\\")) {
      // Cygwin doesn't like upper case drives -> try lower case drive
      try {
        fileStr = absolute.getPath();
        fileStr =   fileStr.substring(0, 1).toLowerCase() 
                  + fileStr.substring(1);
        result = createRelativePath(new File(fileStr));
      }
      catch (Exception e) {
        // no luck with Cygwin workaround, convert it like it is
        result = createRelativePath(absolute);
      }
    }
    else {
      result = createRelativePath(absolute);
    }

    return result;
  }

  /**
   * Converts a File's absolute path to a path relative to the user
   * (ie start) directory.
   * 
   * @param absolute the File to convert to relative path
   * @return a File with a path that is relative to the user's directory
   * @exception Exception if the path cannot be constructed
   */
protected:
  static File createRelativePath(File absolute) throws Exception {
    File userDir = new File(System.getProperty("user.dir"));
    string userPath = userDir.getAbsolutePath() + File.separator;
    string targetPath = (new File(absolute.getParent())).getPath() 
      + File.separator;
    string fileName = absolute.getName();
    StringBuffer relativePath = new StringBuffer();
    //    relativePath.append("."+File.separator);
    //    System.err.println("User dir "+userPath);
    //    System.err.println("Target path "+targetPath);
    
    // file is in user dir (or subdir)
    int subdir = targetPath.indexOf(userPath);
    if (subdir == 0) {
      if (userPath.length() == targetPath.length()) {
	relativePath.append(fileName);
      } else {
	int ll = userPath.length();
	relativePath.append(targetPath.substring(ll));
	relativePath.append(fileName);
      }
    } else {
      int sepCount = 0;
      string temp = new String(userPath);
      while (temp.indexOf(File.separator) != -1) {
	int ind = temp.indexOf(File.separator);
	sepCount++;
	temp = temp.substring(ind+1, temp.length());
      }
      
      string targetTemp = new String(targetPath);
      string userTemp = new String(userPath);
      int tcount = 0;
      while (targetTemp.indexOf(File.separator) != -1) {
	int ind = targetTemp.indexOf(File.separator);
	int ind2 = userTemp.indexOf(File.separator);
	string tpart = targetTemp.substring(0,ind+1);
	string upart = userTemp.substring(0,ind2+1);
	if (tpart.compareTo(upart) != 0) {
	  if (tcount == 0) {
	    tcount = -1;
	  }
	  break;
	}
	tcount++;
	targetTemp = targetTemp.substring(ind+1, targetTemp.length());
	userTemp = userTemp.substring(ind2+1, userTemp.length());
      }
      if (tcount == -1) {
	// then target file is probably on another drive (under windows)
	throw Exception("Can't construct a path to file relative to user "
			    +"dir.");
      }
      if (targetTemp.indexOf(File.separator) == -1) {
	targetTemp = "";
      }
      for (int i = 0; i < sepCount - tcount; i++) {
	relativePath.append(".."+File.separator);
      }
      relativePath.append(targetTemp + fileName);
    }
    //    System.err.println("new path : "+relativePath.toString());
    return new File(relativePath.toString());
  }
  
  /**
   * Implements computation of the kth-smallest element according
   * to Manber's "Introduction to Algorithms".
   *
   * @param array the array of integers
   * @param index the index into the array of integers
   * @param left the first index of the subset 
   * @param right the last index of the subset 
   * @param k the value of k
   *
   * @return the index of the kth-smallest element
   */
  //@ requires 0 <= first && first <= right && right < array.length;
private:
  static int select(/*@non_NULL@*/ int[] array, /*@non_NULL@*/ int[] index, 
                            int left, int right, int k) {
    
    if (left == right) {
      return left;
    } else {
      int middle = partition(array, index, left, right);
      if ((middle - left + 1) >= k) {
        return select(array, index, left, middle, k);
      } else {
        return select(array, index, middle + 1, right, k - (middle - left + 1));
      }
    }
  }
 
public: 
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.60 $");
  }
};


/**
 * Main method for testing this class.
 *
 * @param ops some dummy options
 */
static void main(String[] ops) {

  double[] doublesWithNaN = {4.5, 6.7, Double.NaN, 3.4, 4.8, 1.2, 3.4};
  double[] doubles = {4.5, 6.7, 6.7, 3.4, 4.8, 1.2, 3.4, 6.7, 6.7, 3.4};
  int[] ints = {12, 6, 2, 18, 16, 6, 7, 5, 18, 18, 17};

  try {

    // Option handling
    System.out.println("First option split up:");
    if (ops.length > 0) {
      String[] firstOptionSplitUp = Utils.splitOptions(ops[0]);
      for (int i = 0; i < firstOptionSplitUp.length; i ++) {
	System.out.println(firstOptionSplitUp[i]);
      }
    }					       
    System.out.println("Partitioned options: ");
    String[] partitionedOptions = Utils.partitionOptions(ops);
    for (int i  = 0; i < partitionedOptions.length; i++) {
      System.out.println(partitionedOptions[i]);
    }
    System.out.println("Get position of flag -f: " + Utils.getOptionPos('f', ops));
    System.out.println("Get flag -f: " + Utils.getFlag('f', ops));
    System.out.println("Get position of option -o: " + Utils.getOptionPos('o', ops));
    System.out.println("Get option -o: " + Utils.getOption('o', ops));
    System.out.println("Checking for remaining options... ");
    Utils.checkForRemainingOptions(ops);
      
    // Statistics
    System.out.println("Original array with NaN (doubles): ");
    for (int i = 0; i < doublesWithNaN.length; i++) {
      System.out.print(doublesWithNaN[i] + " ");
    }
    System.out.println();
    System.out.println("Original array (doubles): ");
    for (int i = 0; i < doubles.length; i++) {
      System.out.print(doubles[i] + " ");
    }
    System.out.println();
    System.out.println("Original array (ints): ");
    for (int i = 0; i < ints.length; i++) {
      System.out.print(ints[i] + " ");
    }
    System.out.println();
    System.out.println("Correlation: " + Utils.correlation(doubles, doubles, 
							   doubles.length));
    System.out.println("Mean: " + Utils.mean(doubles));
    System.out.println("Variance: " + Utils.variance(doubles));
    System.out.println("Sum (doubles): " + Utils.sum(doubles));
    System.out.println("Sum (ints): " + Utils.sum(ints));
    System.out.println("Max index (doubles): " + Utils.maxIndex(doubles));
    System.out.println("Max index (ints): " + Utils.maxIndex(ints));
    System.out.println("Min index (doubles): " + Utils.minIndex(doubles));
    System.out.println("Min index (ints): " + Utils.minIndex(ints));
    System.out.println("Median (doubles): " + 
		       Utils.kthSmallestValue(doubles, doubles.length / 2));
    System.out.println("Median (ints): " + 
		       Utils.kthSmallestValue(ints, ints.length / 2));

    // Sorting and normalizing
    System.out.println("Sorted array with NaN (doubles): ");
    int[] sorted = Utils.sort(doublesWithNaN);
    for (int i = 0; i < doublesWithNaN.length; i++) {
      System.out.print(doublesWithNaN[sorted[i]] + " ");
    }
    System.out.println();
    System.out.println("Sorted array (doubles): ");
    sorted = Utils.sort(doubles);
    for (int i = 0; i < doubles.length; i++) {
      System.out.print(doubles[sorted[i]] + " ");
    }
    System.out.println();
    System.out.println("Sorted array (ints): ");
    sorted = Utils.sort(ints);
    for (int i = 0; i < ints.length; i++) {
      System.out.print(ints[sorted[i]] + " ");
    }
    System.out.println();
    System.out.println("Indices from stable sort (doubles): ");
    sorted = Utils.stableSort(doubles);
    for (int i = 0; i < doubles.length; i++) {
      System.out.print(sorted[i] + " ");
    }
    System.out.println();
    System.out.println("Indices from sort (ints): ");
    sorted = Utils.sort(ints);
    for (int i = 0; i < ints.length; i++) {
      System.out.print(sorted[i] + " ");
    }
    System.out.println();
    System.out.println("Normalized array (doubles): ");
    Utils.normalize(doubles);
    for (int i = 0; i < doubles.length; i++) {
      System.out.print(doubles[i] + " ");
    }
    System.out.println();
    System.out.println("Normalized again (doubles): ");
    Utils.normalize(doubles, Utils.sum(doubles));
    for (int i = 0; i < doubles.length; i++) {
      System.out.print(doubles[i] + " ");
    }
    System.out.println();
      
    // Pretty-printing
    System.out.println("-4.58: " + Utils.doubleToString(-4.57826535, 2));
    System.out.println("-6.78: " + Utils.doubleToString(-6.78214234, 6,2));
      
    // Comparisons
    System.out.println("5.70001 == 5.7 ? " + Utils.eq(5.70001, 5.7));
    System.out.println("5.70001 > 5.7 ? " + Utils.gr(5.70001, 5.7));
    System.out.println("5.70001 >= 5.7 ? " + Utils.grOrEq(5.70001, 5.7));
    System.out.println("5.7 < 5.70001 ? " + Utils.sm(5.7, 5.70001));
    System.out.println("5.7 <= 5.70001 ? " + Utils.smOrEq(5.7, 5.70001));
      
    // Math
    System.out.println("Info (ints): " + Utils.info(ints));
    System.out.println("log2(4.6): " + Utils.log2(4.6));
    System.out.println("5 * log(5): " + Utils.xlogx(5));
    System.out.println("5.5 rounded: " + Utils.round(5.5));
    System.out.println("5.55555 rounded to 2 decimal places: " + 
		       Utils.roundDouble(5.55555, 2));
      
    // Arrays
    System.out.println("Array-Dimensions of 'new int[][]': " + Utils.getArrayDimensions(new int[][]{}));
    System.out.println("Array-Dimensions of 'new int[][]{{1,2,3},{4,5,6}}': " + Utils.getArrayDimensions(new int[][]{{1,2,3},{4,5,6}}));
    String[][][] s = new String[3][4][];
    System.out.println("Array-Dimensions of 'new String[3][4][]': " + Utils.getArrayDimensions(s));
  } catch (Exception e) {
    e.printStackTrace();
  }
}
  
