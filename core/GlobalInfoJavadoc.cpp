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
 * GlobalInfoJavadoc.cpp
 * Copyright (C) 2006 University of Waikato, Hamilton, New Zealand
 */

// package weka.core;

// import java.lang.reflect.Method;

/**
 * Generates Javadoc comments from the class's globalInfo method. Can 
 * automatically update the comments if they're surrounded by
 * the GLOBALINFO_STARTTAG and GLOBALINFO_ENDTAG (the indention is determined via
 * the GLOBALINFO_STARTTAG). <p/>
 * 
 <!-- options-start -->
 * Valid options are: <p/>
 * 
 * <pre> -W &lt;classname&gt;
 *  The class to load.</pre>
 * 
 * <pre> -nostars
 *  Suppresses the '*' in the Javadoc.</pre>
 * 
 * <pre> -dir &lt;dir&gt;
 *  The directory above the package hierarchy of the class.</pre>
 * 
 * <pre> -silent
 *  Suppresses printing in the console.</pre>
 * 
 <!-- options-end -->
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.7 $
 * @see #GLOBALINFO_METHOD
 * @see #GLOBALINFO_STARTTAG
 * @see #GLOBALINFO_ENDTAG
 */
class GlobalInfoJavadoc : public Javadoc {
public:
  /** the globalInfo method name */
  const static string GLOBALINFO_METHOD = "globalInfo";
  
  /** the start comment tag for inserting the generated Javadoc */
  const static string GLOBALINFO_STARTTAG = "<!-- globalinfo-start -->";
  
  /** the end comment tag for inserting the generated Javadoc */
  const static string GLOBALINFO_ENDTAG = "<!-- globalinfo-end -->";
  
  /**
   * default constructor 
   */
  GlobalInfoJavadoc() {
    super();
    
    m_StartTag    = new String[1];
    m_EndTag      = new String[1];
    m_StartTag[0] = GLOBALINFO_STARTTAG;
    m_EndTag[0]   = GLOBALINFO_ENDTAG;
  }
  
  /**
   * generates and returns the Javadoc for the specified start/end tag pair.
   * 
   * @param index	the index in the start/end tag array
   * @return		the generated Javadoc
   * @throws Exception 	in case the generation fails
   */
protected:
  string generateJavadoc(int index) throws Exception {
    String		result;
    Method		method;
    
    result = "";
    
    if (index == 0) {
      if (!canInstantiateClass())
	return result;
	    
      try {
	method = getInstance().getClass().getMethod(GLOBALINFO_METHOD, (Class[]) NULL);
      }
      catch (Exception e) {
	// no method "globalInfo"
	return result;
      }
      
      // retrieve global info
      result = toHTML((String) method.invoke(getInstance(), (Object[]) NULL));
      result = result.trim() + "\n<p/>\n";
      
      // stars?
      if (getUseStars()) 
	result = indent(result, 1, "* ");
    }
    
    return result;
  }
  
public:
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.7 $");
  }
  
  /**
   * Parses the given commandline parameters and generates the Javadoc.
   * 
   * @param args	the commandline parameters for the object
   */
  static void main(String[] args) {
    runJavadoc(new GlobalInfoJavadoc(), args);
  }
};
