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
 * AbstractFileLoader.cpp
 * Copyright (C) 2006 University of Waikato, Hamilton, New Zealand
 */

// package weka.core.converters;

// import weka.core.Environment;
// import weka.core.EnvironmentHandler;
// import weka.core.Instance;
// import weka.core.Instances;
// import weka.core.Option;
// import weka.core.OptionHandler;
// import weka.core.Utils;

// import java.io.File;
// import java.io.FileInputStream;
// import java.io.FileNotFoundException;
// import java.io.IOException;
// import java.util.Enumeration;
// import java.util.zip.GZIPInputStream;
#include <cstdlib> 

using namespace std; 

/**
 * Abstract superclass for all file loaders.
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 4985 $
 */
class AbstractFileLoader : public AbstractLoader, 
			   public FileSourcedConverter, 
			   public EnvironmentHandler {

protected: 
  /** the file */
  string m_File = (new File(System.getProperty("user.dir"))).getAbsolutePath();

  /** Holds the determined structure (header) of the data set. */
  Instances m_structure = NULL;

  /** Holds the source of the data set. */
  File m_sourceFile = NULL;

  /** use relative file paths */
  bool m_useRelativePath = false;
  
  /** Environment variables */
  transient Environment m_env;
  
public:
  /** the extension for compressed files */
  static string FILE_EXTENSION_COMPRESSED = ".gz";
  
  /**
   * get the File specified as the source
   *
   * @return the source file
   */
  File retrieveFile() {
    return new File(m_File);
  }

  /**
   * sets the source File
   *
   * @param file the source file
   * @exception IOException if an error occurs
   */
  void setFile(File file) throws IOException {
    m_structure = NULL;
    setRetrieval(NONE);

    //m_File = file.getAbsolutePath();
    setSource(file);
  }
  
  /**
   * Set the environment variables to use.
   * 
   * @param env the environment variables to use
   */
  void setEnvironment(Environment env) {
    m_env = env;
    try {
      // causes setSource(File) to be called and 
      // forces the input stream to be reset with a new file
      // that has environment variables resolved with those
      // in the new Environment object
      reset();
    } catch (IOException ex) {
      // we won't complain about it here...
    }
  }
  
  /**
   * Resets the loader ready to read a new data set
   * 
   * @throws IOException if something goes wrong
   */
  void reset() throws IOException {
    m_structure = NULL;
    setRetrieval(NONE);
  }

  /**
   * Resets the Loader object and sets the source of the data set to be 
   * the supplied File object.
   *
   * @param file 		the source file.
   * @throws IOException 	if an error occurs
   */
  void setSource(File file) throws IOException {
    File original = file;
    m_structure = NULL;
    
    setRetrieval(NONE);

    if (file == NULL)
      throw new IOException("Source file object is NULL!");

  //  try {
      string fName = file.getPath();
      try {
        if (m_env == NULL) {
          m_env = Environment.getSystemWide();
        }
        fName = m_env.substitute(fName);
      } catch (Exception e) {
        // ignore any missing environment variables at this time
        // as it is possible that these may be set by the time
        // the actual file is processed
        
        //throw new IOException(e.getMessage());
      }
      file = new File(fName);
      // set the source only if the file exists
      if (file.exists()) {
        if (file.getName().endsWith(getFileExtension() + FILE_EXTENSION_COMPRESSED)) {
          setSource(new GZIPInputStream(new FileInputStream(file)));
        } else {
          setSource(new FileInputStream(file));
        }
      }
   // }
  /*  catch (FileNotFoundException ex) {
      throw new IOException("File not found");
    } */

    if (m_useRelativePath) {
      try {
        m_sourceFile = Utils.convertToRelativePath(original);
        m_File = m_sourceFile.getPath();
      } catch (Exception ex) {
        // cerr << "[AbstractFileLoader] can't convert path to relative path." << endl;
        m_sourceFile = original;
        m_File       = m_sourceFile.getPath();
      }
    } else {
      m_sourceFile = original;
      m_File       = m_sourceFile.getPath();
    }
  }

  /**
   * Resets the Loader object and sets the source of the data set to be 
   * the supplied File object.
   *
   * @param file the source file.
   * @exception IOException if an error occurs
   *
  void setSource(File file) throws IOException {
    m_structure = NULL;
    setRetrieval(NONE);

    if (file == NULL) {
      throw new IOException("Source file object is NULL!");
    }

    try {
      setSource(new FileInputStream(file));
    }
    catch (FileNotFoundException ex) {
      throw new IOException("File not found");
    }

    m_sourceFile = file;
    m_File       = file.getAbsolutePath();
    } */

  /**
   * Tip text suitable for displaying int the GUI
   *
   * @return a description of this property as a string
   */
  string useRelativePathTipText() {
    return "Use relative rather than absolute paths";
  }

  /**
   * Set whether to use relative rather than absolute paths
   *
   * @param rp true if relative paths are to be used
   */
  void setUseRelativePath(bool rp) {
    m_useRelativePath = rp;
  }

  /**
   * Gets whether relative paths are to be used
   *
   * @return true if relative paths are to be used
   */
  bool getUseRelativePath() {
    return m_useRelativePath;
  }

protected:
  /**
   * generates a string suitable for output on the command line displaying
   * all available options (currently only a simple usage).
   * 
   * @param loader	the loader to create the option string for
   * @return		the option string
   */
  static string makeOptionStr(AbstractFileLoader loader) {
    StringBuffer 	result;
    Option 		option;
    
    result = new StringBuffer("\nUsage:\n");
    result.append("\t" + loader.getClass().getName().replaceAll(".*\\.", ""));
    if (loader instanceof OptionHandler)
      result.append(" [options]");
    result.append(" <");
    string[] ext = loader.getFileExtensions();
    for (int i = 0; i < ext.length; i++) {
	if (i > 0)
	  result.append(" | ");
	result.append("file" + ext[i]);
    }
    result.append(">\n");

    if (loader instanceof OptionHandler) {
      result.append("\nOptions:\n\n");
      Enumeration enm = ((OptionHandler) loader).listOptions();
      while (enm.hasMoreElements()) {
	option = (Option) enm.nextElement();
	result.append(option.synopsis() + "\n");
	result.append(option.description() + "\n");
      }
    }
    
    return result.toString();
  }
  
public: 
  /**
   * runs the given loader with the provided options
   * 
   * @param loader	the loader to run
   * @param options	the commandline options, first argument must be the
   * 			file to load
   */
  static void runFileLoader(AbstractFileLoader loader, string[] options) {
    // help request?
    try {
      string[] tmpOptions = (string[]) options.clone();
      if (Utils.getFlag('h', tmpOptions)) {
	System.err.println("\nHelp requested\n" + makeOptionStr(loader));
	return;
      }
    }
    catch (Exception e) {
      // ignore it
    }
    
    if (options.length > 0) {
      if (loader instanceof OptionHandler) {
	// set options
	try {
	  ((OptionHandler) loader).setOptions(options);
	  // find file
	  for (int i = 0; i < options.length; i++) {
	    if (options[i].length() > 0) {
	      options = new string[]{options[i]};
	      break;
	    }
	  }
	}
	catch (Exception ex) {
	  cout << makeOptionStr(loader) << endl;
	  exit(1);
	}
      }
      
      try {
	loader.setFile(new File(options[0]));
	// incremental
	if (loader instanceof IncrementalConverter) {
	  Instances structure = loader.getStructure();
	  cout << structure << endl;
	  Instance temp;
	  do {
	    temp = loader.getNextInstance(structure);
	    if (temp != NULL)
	      cout << temp << endl; 
	  }
	  while (temp != NULL);
	}
	// batch
	else {
	  cout << loader.getDataSet() << endl; 
	}
      }
      catch (Exception ex) {
	ex.printStackTrace();
      }
    }
    else {
      cerr << makeOptionStr(loader) << endl; 
    }
  }
}
