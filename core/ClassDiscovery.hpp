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
#ifndef _CPP_WEKA_CLASSDISCOVERY_H_
#define _CPP_WEKA_CLASSDISCOVERY_H_

#include <vector>
// import java.io.File;
// import java.lang.reflect.Modifier;
// import java.net.URL;
// import java.util.Collections;
// import java.util.Comparator;
// import java.util.Enumeration;
// import java.util.HashSet;
// import java.util.Hashtable;
// import java.util.StringTokenizer;
// import java.util.Vector;
// import java.util.jar.JarEntry;
// import java.util.jar.JarFile;

/**
 * This class is used for discovering classes that implement a certain
 * interface or a derived from a certain class.
 *
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 5377 $
 * @see StringCompare
 */
class ClassDiscovery : public RevisionHandler {

  /** whether to output some debug information. */
public:
  const static bool VERBOSE = false;
  
  /** for caching queries (classname+packagename &lt;-&gt; Vector with classnames). */
protected:
  static Hashtable<String,Vector> m_Cache;
  
public:
  /** notify if VERBOSE is still on */
  static {
    if (VERBOSE)
      System.err.println(ClassDiscovery.class.getName() + ": VERBOSE ON");
  }
  
  /**
   * Checks whether the "otherclass" is a subclass of the given "superclass".
   * 
   * @param superclass      the superclass to check against
   * @param otherclass      this class is checked whether it is a subclass
   *                        of the the superclass
   * @return                TRUE if "otherclass" is a true subclass
   */
    static bool isSubclass(string superclass, string otherclass);
  
  /**
   * Checks whether the "otherclass" is a subclass of the given "superclass".
   * 
   * @param superclass      the superclass to check against
   * @param otherclass      this class is checked whether it is a subclass
   *                        of the the superclass
   * @return                TRUE if "otherclass" is a true subclass
   */
    static bool isSubclass(Class superclass, Class otherclass);
  
  /**
   * Checks whether the given class implements the given interface.
   * 
   * @param intf      the interface to look for in the given class
   * @param cls       the class to check for the interface
   * @return          TRUE if the class contains the interface 
   */
    static bool hasInterface(string intf, string cls);
  
  /**
   * Checks whether the given class implements the given interface.
   * 
   * @param intf      the interface to look for in the given class
   * @param cls       the class to check for the interface
   * @return          TRUE if the class contains the interface 
   */
    static bool hasInterface(Class intf, Class cls);
  
  /**
   * If the given package can be found in this part of the classpath then 
   * an URL object is returned, otherwise <code>NULL</code>.
   * 
   * @param classpathPart     the part of the classpath to look for the package
   * @param pkgname           the package to look for
   * @return                  if found, the url as string, otherwise NULL
   */
protected:
    static URL getURL(string classpathPart, string pkgname);
  /**
   * Checks the given packages for classes that inherited from the given class,
   * in case it's a class, or implement this class, in case it's an interface.
   *
   * @param classname       the class/interface to look for
   * @param pkgnames        the packages to search in
   * @return                a list with all the found classnames
   */
    static Vector find(string classname, String[] pkgnames);

  /**
   * Checks the given package for classes that inherited from the given class,
   * in case it's a class, or implement this class, in case it's an interface.
   *
   * @param classname       the class/interface to look for
   * @param pkgname         the package to search in
   * @return                a list with all the found classnames
   */
    static Vector find(string classname, string pkgname);

  /**
   * Checks the given packages for classes that inherited from the given class,
   * in case it's a class, or implement this class, in case it's an interface.
   *
   * @param cls             the class/interface to look for
   * @param pkgnames        the packages to search in
   * @return                a list with all the found classnames
   */
    static Vector find(Class cls, String[] pkgnames);

  /**
   * Checks the given package for classes that inherited from the given class,
   * in case it's a class, or implement this class, in case it's an interface.
   *
   * @param cls             the class/interface to look for
   * @param pkgname         the package to search in
   * @return                a list with all the found classnames
   */
    static Vector find(Class cls, string pkgname);

  /**
   * adds all the sub-directories recursively to the list.
   * 
   * @param prefix	the path prefix
   * @param dir		the directory to look in for sub-dirs
   * @param list	the current list of sub-dirs
   * @return		the new list of sub-dirs
   */
protected:
    static HashSet getSubDirectories(string prefix, File dir, HashSet list);

public:
  /**
   * Lists all packages it can find in the classpath.
   *
   * @return                a list with all the found packages
   */
    static Vector findPackages();

  /**
   * initializes the cache for the classnames.
   */
protected:
  inline static void initCache() {
    if (m_Cache == NULL)
      m_Cache = new Hashtable<String,Vector>();
  }
  
  /**
   * adds the list of classnames to the cache.
   * 
   * @param cls		the class to cache the classnames for
   * @param pkgname	the package name the classes were found in
   * @param classnames	the list of classnames to cache
   */
    static void addCache(Class cls, string pkgname, Vector classnames);
  
  /**
   * returns the list of classnames associated with this class and package, if
   * available, otherwise NULL.
   * 
   * @param cls		the class to get the classnames for
   * @param pkgname	the package name for the classes 
   * @return		the classnames if found, otherwise NULL
   */
    static Vector getCache(Class cls, string pkgname);

public:
  /**
   * clears the cache for class/classnames relation.
   */
    static void clearCache();
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  inline string getRevision() {
    return RevisionUtils.extract("$Revision: 5377 $");
  }
 
  /**
   * compares two strings. The following order is used:<br/>
   * <ul>
   *    <li>case insensitive</li>
   *    <li>german umlauts (&auml; , &ouml; etc.) or other non-ASCII letters
   *    are treated as special chars</li>
   *    <li>special chars &lt; numbers &lt; letters</li>
   * </ul>
   */
  class StringCompare : public Comparator, 
			public RevisionHandler {

    /**
     * appends blanks to the string if its shorter than <code>len</code>.
     * 
     * @param s		the string to pad
     * @param len	the minimum length for the string to have
     * @return		the padded string
     */
  private:
      string fillUp(string s, int len);
    
    /**
     * returns the group of the character: 0=special char, 1=number, 2=letter.
     * 
     * @param c		the character to check
     * @return		the group
     */
      int charGroup(char c);

  public:    
    /**
     * Compares its two arguments for order.
     * 
     * @param o1	the first object
     * @param o2	the second object
     * @return		-1 if o1&lt;o2, 0 if o1=o2 and 1 if o1&;gt;o2
     */    
      int compare(Object o1, Object o2);
    
    /**
     * Indicates whether some other object is "equal to" this Comparator. 
     * 
     * @param obj	the object to compare with this Comparator
     * @return		true if the object is a StringCompare object as well
     */
    inline bool equals(Object obj) {
      return (obj instanceof StringCompare);
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 5377 $");
    }
  }

/**
 * Possible calls:
 * <ul>
 *    <li>
 *      weka.core.ClassDiscovery &lt;packages&gt;<br/>
 *      Prints all the packages in the current classpath
 *    </li>
 *    <li>
 *      weka.core.ClassDiscovery &lt;classname&gt; &lt;packagename(s)&gt;<br/>
 *      Prints the classes it found.
 *    </li>
 * </ul>
 * 
 * @param args	the commandline arguments
 */
      static void main(String[] args);

};

#endif
