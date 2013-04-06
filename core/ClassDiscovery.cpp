#include "ClassDiscovery.hpp"

static bool ClassDiscovery::isSubclass(string superclass, string otherclass) {
    try {
      return isSubclass(Class.forName(superclass), Class.forName(otherclass));
    }
    catch (Exception e) {
      return false;
    }
  }
  
static bool ClassDiscovery::isSubclass(Class superclass, Class otherclass) {
    Class       currentclass;
    bool     result;
    
    result       = false;
    currentclass = otherclass;
    do {
      result = currentclass.equals(superclass);
      
      // topmost class reached?
      if (currentclass.equals(Object.class))
        break;
      
      if (!result)
        currentclass = currentclass.getSuperclass(); 
    } 
    while (!result);
    
    return result;
  }
  
static bool ClassDiscovery::hasInterface(string intf, string cls) {
    try {
      return hasInterface(Class.forName(intf), Class.forName(cls));
    }
    catch (Exception e) {
      return false;
    }
  }
  
static bool ClassDiscovery::hasInterface(Class intf, Class cls) {
    Class[]       intfs;
    int           i;
    bool       result;
    Class         currentclass;
    
    result       = false;
    currentclass = cls;
    do {
      // check all the interfaces, this class implements
      intfs = currentclass.getInterfaces();
      for (i = 0; i < intfs.length; i++) {
        if (intfs[i].equals(intf)) {
          result = true;
          break;
        }
      }

      // get parent class
      if (!result) {
        currentclass = currentclass.getSuperclass();
        
        // topmost class reached or no superclass?
        if ( (currentclass == NULL) || (currentclass.equals(Object.class)) )
          break;
      }
    } 
    while (!result);
      
    return result;
  }
  
static URL ClassDiscovery::getURL(string classpathPart, string pkgname) {
    string              urlStr;
    URL                 result;
    File                classpathFile;
    File                file;
    JarFile             jarfile;
    Enumeration         enm;
    string              pkgnameTmp;
    
    result = NULL;
    urlStr = NULL;

    try {
      classpathFile = new File(classpathPart);
      
      // directory or jar?
      if (classpathFile.isDirectory()) {
        // does the package exist in this directory?
        file = new File(classpathPart + pkgname);
        if (file.exists())
          urlStr = "file:" + classpathPart + pkgname;
      }
      else {
        // is package actually included in jar?
        jarfile    = new JarFile(classpathPart);
        enm        = jarfile.entries();
        pkgnameTmp = pkgname.substring(1);   // remove the leading "/"
        while (enm.hasMoreElements()) {
          if (enm.nextElement().toString().startsWith(pkgnameTmp)) {
            urlStr = "jar:file:" + classpathPart + "!" + pkgname;
            break;
          }
        }
      }
    }
    catch (Exception e) {
      // ignore
    }
    
    // try to generate URL from url string
    if (urlStr != NULL) {
      try {
        result = new URL(urlStr);
      }
      catch (Exception e) {
        System.err.println(
            "Trying to create URL from '" + urlStr 
            + "' generates this exception:\n" + e);
        result = NULL;
      }
    }

    return result;
  }

static Vector ClassDiscovery::find(string classname, String[] pkgnames) {
    Vector      result;
    Class       cls;

    result = new Vector();

    try {
      cls    = Class.forName(classname);
      result = find(cls, pkgnames);
    }
    catch (Exception e) {
      e.printStackTrace();
    }

    return result;
  }

static Vector ClassDiscovery::find(string classname, string pkgname) {
    Vector      result;
    Class       cls;

    result = new Vector();

    try {
      cls    = Class.forName(classname);
      result = find(cls, pkgname);
    }
    catch (Exception e) {
      e.printStackTrace();
    }

    return result;
  }

static Vector ClassDiscovery::find(Class cls, String[] pkgnames) {
    Vector	result;
    int		i;
    HashSet	names;

    result = new Vector();

    names = new HashSet();
    for (i = 0; i < pkgnames.length; i++)
      names.addAll(find(cls, pkgnames[i]));

    // sort result
    result.addAll(names);
    Collections.sort(result, new StringCompare());

    return result;
  }

static Vector ClassDiscovery::find(Class cls, string pkgname) {
    Vector                result;
    StringTokenizer       tok;
    string                part;
    string                pkgpath;
    File                  dir;
    File[]                files;
    URL                   url;
    int                   i;
    Class                 clsNew;
    string                classname;
    JarFile               jar;
    JarEntry              entry;
    Enumeration           enm;


    // already cached?
    result = getCache(cls, pkgname);
    
    if (result == NULL) {
      result = new Vector();

      if (VERBOSE)
	System.out.println(
	    "Searching for '" + cls.getName() + "' in '" + pkgname + "':");

      // turn package into path
      pkgpath = pkgname.replaceAll("\\.", "/");

      // check all parts of the classpath, to include additional classes from
      // "parallel" directories/jars, not just the first occurence
      tok = new StringTokenizer(
	  System.getProperty("java.class.path"), 
	  System.getProperty("path.separator"));

      while (tok.hasMoreTokens()) {
	part = tok.nextToken();
	if (VERBOSE)
	  System.out.println("Classpath-part: " + part);

	// does package exist in this part of the classpath?
	url = getURL(part, "/" + pkgpath);
	if (VERBOSE) {
	  if (url == NULL)
	    System.out.println("   " + pkgpath + " NOT FOUND");
	  else
	    System.out.println("   " + pkgpath + " FOUND");
	}
	if (url == NULL)
	  continue;

	// find classes
	dir = new File(part + "/" + pkgpath);
	if (dir.exists()) {
	  files = dir.listFiles();
	  for (i = 0; i < files.length; i++) {
	    // only class files
	    if (    (!files[i].isFile()) 
		|| (!files[i].getName().endsWith(".class")) )
	      continue;

	    try {
	      classname =   pkgname + "." 
	      + files[i].getName().replaceAll(".*/", "")
	      .replaceAll("\\.class", "");
	      result.add(classname);
	    }
	    catch (Exception e) {
	      e.printStackTrace();
	    }
	  }
	}
	else {
	  try {
	    jar = new JarFile(part);
	    enm = jar.entries();
	    while (enm.hasMoreElements()) {
	      entry = (JarEntry) enm.nextElement();

	      // only class files
	      if (    (entry.isDirectory())
		  || (!entry.getName().endsWith(".class")) )
		continue;

	      classname = entry.getName().replaceAll("\\.class", "");

	      // only classes in the particular package
	      if (!classname.startsWith(pkgpath))
		continue;

	      // no sub-package
	      if (classname.substring(pkgpath.length() + 1).indexOf("/") > -1)
		continue;

	      result.add(classname.replaceAll("/", "."));
	    }
	  }
	  catch (Exception e) {
	    e.printStackTrace();
	  }
	}
      }

      // check classes
      i = 0;
      while (i < result.size()) {
	try {
	  clsNew = Class.forName((String) result.get(i));

	  // no abstract classes
	  if (Modifier.isAbstract(clsNew.getModifiers()))
	    result.remove(i);
	  // must implement interface
	  else if ( (cls.isInterface()) && (!hasInterface(cls, clsNew)) )
	    result.remove(i);
	  // must be derived from class
	  else if ( (!cls.isInterface()) && (!isSubclass(cls, clsNew)) )
	    result.remove(i);
	  else
	    i++;
	}
	catch (Throwable e) {
	  System.err.println("Checking class: " + result.get(i));
	  e.printStackTrace();
	  result.remove(i);
	}
      }

      // sort result
      Collections.sort(result, new StringCompare());

      // add to cache
      addCache(cls, pkgname, result);
    }

    return result;
  }

static HashSet ClassDiscovery::getSubDirectories(string prefix, File dir, HashSet list) {
    File[]	files;
    int		i;
    string 	newPrefix;
    
    // add directory to the list
    if (prefix == NULL)
      newPrefix = "";
    else if (prefix.length() == 0)
      newPrefix = dir.getName();
    else
      newPrefix = prefix + "." + dir.getName();

    if (newPrefix.length() != 0)
      list.add(newPrefix);
    
    // search for sub-directories
    files = dir.listFiles();
    if (files != NULL) {
      for (i = 0; i < files.length; i++) {
	if (files[i].isDirectory())
	  list = getSubDirectories(newPrefix, files[i], list);
      }
    }
      
    return list;
  }

static Vector ClassDiscovery::findPackages() {
    Vector		result;
    StringTokenizer	tok;
    String		part;
    File		file;
    JarFile		jar;
    JarEntry		entry;
    Enumeration		enm;
    HashSet		set;

    result = new Vector();
    set    = new HashSet();
    
    // check all parts of the classpath, to include additional classes from
    // "parallel" directories/jars, not just the first occurence
    tok = new StringTokenizer(
        System.getProperty("java.class.path"), 
        System.getProperty("path.separator"));

    while (tok.hasMoreTokens()) {
      part = tok.nextToken();
      if (VERBOSE)
        System.out.println("Classpath-part: " + part);
      
      // find classes
      file = new File(part);
      if (file.isDirectory()) {
	set = getSubDirectories(NULL, file, set);
      }
      else if (file.exists()) {
        try {
          jar = new JarFile(part);
          enm = jar.entries();
          while (enm.hasMoreElements()) {
            entry = (JarEntry) enm.nextElement();
            
            // only directories
            if (entry.isDirectory())
              set.add(entry.getName().replaceAll("/", ".").replaceAll("\\.$", ""));
          }
        }
        catch (Exception e) {
          e.printStackTrace();
        }
      }
    }

    // sort result
    set.remove("META-INF");
    result.addAll(set);
    Collections.sort(result, new StringCompare());

    return result;
  }

static void ClassDiscovery::initCache() {
    if (m_Cache == NULL)
      m_Cache = new Hashtable<String,Vector>();
  }
  
static void ClassDiscovery::addCache(Class cls, string pkgname, Vector classnames) {
    initCache();
    m_Cache.put(cls.getName() + "-" + pkgname, classnames);
  }
  
static Vector ClassDiscovery::getCache(Class cls, string pkgname) {
    initCache();
    return m_Cache.get(cls.getName() + "-" + pkgname);
  }

static void ClassDiscovery::clearCache() {
    initCache();
    m_Cache.clear();
  }

string StringCompare::fillUp(string s, int len) {
      while (s.length() < len)
        s += " ";
      return s;
    }
    
    /**
     * returns the group of the character: 0=special char, 1=number, 2=letter.
     * 
     * @param c		the character to check
     * @return		the group
     */
int StringCompare::charGroup(char c) {
      int         result;
      
      result = 0;
      
      if ( (c >= 'a') && (c <= 'z') )
        result = 2;
      else if ( (c >= '0') && (c <= '9') )
        result = 1;
      
      return result;
    }

int StringCompare::compare(Object o1, Object o2) {
      string        s1;
      string        s2;
      int           i;
      int           result;
      int           v1;
      int           v2;
      
      result = 0;   // they're equal
      
      // get lower case string
      s1 = o1.toString().toLowerCase();
      s2 = o2.toString().toLowerCase();
      
      // same length
      s1 = fillUp(s1, s2.length());
      s2 = fillUp(s2, s1.length());
      
      for (i = 0; i < s1.length(); i++) {
        // same char?
        if (s1.charAt(i) == s2.charAt(i)) {
          result = 0;
        }
        else {
          v1 = charGroup(s1.charAt(i));
          v2 = charGroup(s2.charAt(i));
          
          // different type (special, number, letter)?
          if (v1 != v2) {
            if (v1 < v2)
              result = -1;
            else
              result = 1;
          }
          else {
            if (s1.charAt(i) < s2.charAt(i))
              result = -1;
            else
              result = 1;
          }
          
          break;
        }
      }
      
      return result;
    }
    
    /**
     * Indicates whether some other object is "equal to" this Comparator. 
     * 
     * @param obj	the object to compare with this Comparator
     * @return		true if the object is a StringCompare object as well
     */
bool StringCompare::equals(Object obj) {
      return (obj instanceof StringCompare);
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
string StringCompare::getRevision() {
      return RevisionUtils.extract("$Revision: 5377 $");
    }
  }

static void ClassDiscovery::main(String[] args) {
  Vector      	list;
  Vector 		packages;
  int         	i;
  StringTokenizer	tok;
    
  if ((args.length == 1) && (args[0].equals("packages"))) {
    list = findPackages();
    for (i = 0; i < list.size(); i++)
      System.out.println(list.get(i));
  }
  else if (args.length == 2) {
    // packages
    packages = new Vector();
    tok = new StringTokenizer(args[1], ",");
    while (tok.hasMoreTokens())
      packages.add(tok.nextToken());
      
    // search
    list = ClassDiscovery.find(
			       args[0], 
			       (String[]) packages.toArray(new String[packages.size()]));

    // print result, if any
    System.out.println(
		       "Searching for '" + args[0] + "' in '" + args[1] + "':\n" 
		       + "  " + list.size() + " found.");
    for (i = 0; i < list.size(); i++)
      System.out.println("  " + (i+1) + ". " + list.get(i));
  }
  else {
    System.out.println("\nUsage:");
    System.out.println(
		       ClassDiscovery.class.getName() + " packages");
    System.out.println("\tlists all packages in the classpath");
    System.out.println(
		       ClassDiscovery.class.getName() + " <classname> <packagename(s)>");
    System.out.println("\tlists classes derived from/implementing 'classname' that");
    System.out.println("\tcan be found in 'packagename(s)' (comma-separated list");
    System.out.println();
    System.exit(1);
  }
}

