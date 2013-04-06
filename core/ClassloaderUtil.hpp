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
#ifndef _CPP_WEKA_CLASSLOADERUTIL_H_
#define _CPP_WEKA_CLASSLOADERUTIL_H_

#include <iostream>

// import java.io.File;
// import java.io.IOException;
// import java.lang.reflect.Method;
// import java.net.URL;
// import java.net.URLClassLoader;

/**
 * Utility class that can add jar files to the classpath dynamically.
 *
 * @author Mark Hall (mhall{[at]}pentaho{[dot]}org
 * @version  $Revision: 5562 $
 */
class ClassloaderUtil : public RevisionHandler {

  // Parameters
private:
  static final Class[] parameters = new Class[]{URL.class};

  /**
   * Add file to CLASSPATH
   * @param s File name
   * @throws IOException if something goes wrong when adding a file
   */
public:
    static void addFile(string s);

  /**
   * Add file to CLASSPATH
   * @param f  File object
   * @throws IOException if something goes wrong when adding a file
   */
    static void addFile(File f);

  /**
   * Add URL to CLASSPATH
   * @param u URL
   * @throws IOException if something goes wrong when adding a url
   */
    static void addURL(URL u);
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
 inline string getRevision() {
    return RevisionUtils.extract("$Revision: 5562 $");
  }
};
