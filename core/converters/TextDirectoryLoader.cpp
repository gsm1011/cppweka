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
 * TextDirectoryLoader.cpp
 * Copyright (C) 2006 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.converters;

// import weka.core.Attribute;
// import weka.core.FastVector;
// import weka.core.Instance;
// import weka.core.Instances;
// import weka.core.Option;
// import weka.core.OptionHandler;
// import weka.core.RevisionUtils;
// import weka.core.Utils;

// import java.io.BufferedInputStream;
// import java.io.File;
// import java.io.FileInputStream;
// import java.io.IOException;
// import java.util.Enumeration;
// import java.util.Vector;

/**
 <!-- globalinfo-start -->
 * Loads all text files in a directory and uses the subdirectory names as class labels. The content of the text files will be stored in a string attribute, the filename can be stored as well.
 * <p/>
 <!-- globalinfo-end -->
 *
 <!-- options-start -->
 * Valid options are: <p/>
 * 
 * <pre> -D
 *  Enables debug output.
 *  (default: off)</pre>
 * 
 * <pre> -F
 *  Stores the filename in an additional attribute.
 *  (default: off)</pre>
 * 
 * <pre> -dir &lt;directory&gt;
 *  The directory to work on.
 *  (default: current directory)</pre>
 * 
 <!-- options-end -->
 *
 * Based on code from the TextDirectoryToArff tool:
 * <ul>
 *    <li><a href="https://list.scms.waikato.ac.nz/mailman/htdig/wekalist/2002-October/000685.html" target="_blank">Original tool</a></li>
 *    <li><a href="https://list.scms.waikato.ac.nz/mailman/htdig/wekalist/2004-January/002160.html" target="_blank">Current version</a></li>
 *    <li><a href="http://weka.wikispaces.com/ARFF+files+from+Text+Collections" target="_blank">Wiki article</a></li>
 * </ul>
 *
 * @author Ashraf M. Kibriya (amk14 at cs.waikato.ac.nz)
 * @author Richard Kirkby (rkirkby at cs.waikato.ac.nz)
 * @author fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 6768 $
 * @see Loader
 */
class TextDirectoryLoader : public AbstractLoader, 
			    public BatchConverter, 
			    public OptionHandler {
  
  /** for serialization */
  // private static final long serialVersionUID = 2592118773712247647L;
  
protected:
  /** Holds the determined structure (header) of the data set. */
  Instances m_structure = NULL;
  
  /** Holds the source of the data set. */
  File m_sourceFile = new File(System.getProperty("user.dir"));
  
  /** whether to print some debug information */
  bool m_Debug = false;
  
  /** whether to include the filename as an extra attribute */
  bool m_OutputFilename = false;
  
public: 
  /**
   * default constructor
   */
  TextDirectoryLoader() {
    // No instances retrieved yet
    setRetrieval(NONE);
  }
  
  /**
   * Returns a string describing this loader
   * 
   * @return 		a description of the evaluator suitable for
   * 			displaying in the explorer/experimenter gui
   */
  string globalInfo() {
    return 
        "Loads all text files in a directory and uses the subdirectory names "
      + "as class labels. The content of the text files will be stored in a "
      + "string attribute, the filename can be stored as well.";
  }
  
  /** 
   * Lists the available options
   * 
   * @return 		an enumeration of the available options
   */  
  Enumeration listOptions() {
    
    Vector result = new Vector();
    
    result.add(new Option(
	"\tEnables debug output.\n"
	+ "\t(default: off)",
	"D", 0, "-D"));
    
    result.add(new Option(
	"\tStores the filename in an additional attribute.\n"
	+ "\t(default: off)",
	"F", 0, "-F"));
    
    result.add(new Option(
	"\tThe directory to work on.\n"
	+ "\t(default: current directory)",
	"dir", 0, "-dir <directory>"));
    
    return  result.elements();
  }
  
  /** 
   * Parses a given list of options. <p/>
   *
   <!-- options-start -->
   * Valid options are: <p/>
   * 
   * <pre> -D
   *  Enables debug output.
   *  (default: off)</pre>
   * 
   * <pre> -F
   *  Stores the filename in an additional attribute.
   *  (default: off)</pre>
   * 
   * <pre> -dir &lt;directory&gt;
   *  The directory to work on.
   *  (default: current directory)</pre>
   * 
   <!-- options-end -->
   *
   * @param options the options
   * @throws Exception if options cannot be set
   */  
  void setOptions(String[] options) throws Exception {
    setDebug(Utils.getFlag("D", options));
    
    setOutputFilename(Utils.getFlag("F", options));
    
    setDirectory(new File(Utils.getOption("dir", options)));
  }
  
  /** 
   * Gets the setting
   * 
   * @return the current setting
   */  
  String[] getOptions() {
    Vector options = new Vector();
    
    if (getDebug())
      options.add("-D");
    
    if (getOutputFilename())
      options.add("-F");

    options.add("-dir");
    options.add(getDirectory().getAbsolutePath());
    
    return (String[]) options.toArray(new String[options.size()]);
  }
  
  /**
   * Sets whether to print some debug information.
   * 
   * @param value	if true additional debug information will be printed.
   */
  void setDebug(bool value) {
    m_Debug = value;
  }
  
  /**
   * Gets whether additional debug information is printed.
   * 
   * @return		true if additional debug information is printed
   */
  bool getDebug() {
    return m_Debug;
  }
  
  /**
   * the tip text for this property
   * 
   * @return 		the tip text
   */
  string debugTipText(){
    return "Whether to print additional debug information to the console.";
  }
  
  /**
   * Sets whether the filename will be stored as an extra attribute.
   * 
   * @param value	if true the filename will be stored in an extra
   * 			attribute
   */
  void setOutputFilename(bool value) {
    m_OutputFilename = value;
    reset();
  }
  
  /**
   * Gets whether the filename will be stored as an extra attribute.
   * 
   * @return		true if the filename is stored in an extra attribute
   */
  bool getOutputFilename() {
    return m_OutputFilename;
  }
  
  /**
   * the tip text for this property
   * 
   * @return 		the tip text
   */
  string outputFilenameTipText(){
    return "Whether to store the filename in an additional attribute.";
  }
  
  /**
   * Returns a description of the file type, actually it's directories.
   *
   * @return 		a short file description
   */
  string getFileDescription() {
    return "Directories";
  }
  
  /**
   * get the Dir specified as the source
   *
   * @return 		the source directory
   */
  File getDirectory() {
    return new File(m_sourceFile.getAbsolutePath());
  }
  
  /**
   * sets the source directory
   *
   * @param 			dir the source directory
   * @throws IOException 	if an error occurs
   */
  void setDirectory(File dir) throws IOException {
    setSource(dir);
  }
  
  /**
   * Resets the loader ready to read a new data set
   */
  void reset() {
    m_structure = NULL;
    setRetrieval(NONE);
  }
  
  /**
   * Resets the Loader object and sets the source of the data set to be 
   * the supplied File object.
   *
   * @param dir 		the source directory.
   * @throws IOException 	if an error occurs
   */
  void setSource(File dir) throws IOException {
    reset();
    
    if (dir == NULL) {
      throw new IOException("Source directory object is NULL!");
    }
    
    m_sourceFile = dir;
    if (!dir.exists() || !dir.isDirectory())
      throw new IOException("Directory '" + dir + "' not found");
  }
  
  /**
   * Determines and returns (if possible) the structure (internally the 
   * header) of the data set as an empty set of instances.
   *
   * @return 			the structure of the data set as an empty 
   * 				set of Instances
   * @throws IOException 	if an error occurs
   */
  Instances getStructure() throws IOException {
    if (getDirectory() == NULL) {
      throw new IOException("No directory/source has been specified");
    }
    
    // determine class labels, i.e., sub-dirs
    if (m_structure == NULL) {
      string directoryPath = getDirectory().getAbsolutePath();
      FastVector atts = new FastVector();
      FastVector classes = new FastVector();
      
      File dir = new File(directoryPath);
      String[] subdirs = dir.list();
      
      for (int i = 0; i < subdirs.length; i++) {
	File subdir = new File(directoryPath + File.separator + subdirs[i]);
	if (subdir.isDirectory())
	  classes.addElement(subdirs[i]);
      }
      
      atts.addElement(new Attribute("text", (FastVector) NULL));
      if (m_OutputFilename)
	atts.addElement(new Attribute("filename", (FastVector) NULL));
      // make sure that the name of the class attribute is unlikely to 
      // clash with any attribute created via the StringToWordVector filter
      atts.addElement(new Attribute("@@class@@", classes));
      
      string relName = directoryPath.replaceAll("/", "_");
      relName = relName.replaceAll("\\\\", "_").replaceAll(":", "_");
      m_structure = new Instances(relName, atts, 0);    
      m_structure.setClassIndex(m_structure.numAttributes() - 1);
    }
    
    return m_structure;
  }
  
  /**
   * Return the full data set. If the structure hasn't yet been determined
   * by a call to getStructure then method should do so before processing
   * the rest of the data set.
   *
   * @return the structure of the data set as an empty set of Instances
   * @throws IOException if there is no source or parsing fails
   */
  Instances getDataSet() throws IOException {
    if (getDirectory() == NULL)
      throw new IOException("No directory/source has been specified");
    
    string directoryPath = getDirectory().getAbsolutePath();
    FastVector classes = new FastVector();
    Enumeration enm = getStructure().classAttribute().enumerateValues();
    while (enm.hasMoreElements())
      classes.addElement(enm.nextElement());
    
    Instances data = getStructure();
    int fileCount = 0;
    for (int k = 0; k < classes.size(); k++) {
      string subdirPath = (String) classes.elementAt(k);
      File subdir = new File(directoryPath + File.separator + subdirPath);
      String[] files = subdir.list();
      for (int j = 0; j < files.length; j++) {
	try {
	  fileCount++;
	  if (getDebug())
	    System.err.println(
		"processing " + fileCount + " : " + subdirPath + " : " + files[j]); 
	  
	  double[] newInst = NULL;
	  if (m_OutputFilename)
	    newInst = new double[3];
	  else
	    newInst = new double[2];		    
	  File txt = new File(directoryPath + File.separator + subdirPath + File.separator + files[j]);
	  BufferedInputStream is;
	  is = new BufferedInputStream(new FileInputStream(txt));
	  StringBuffer txtStr = new StringBuffer();
	  int c;
	  while ((c = is.read()) != -1) {
	    txtStr.append((char) c);
	  }
	  
	  newInst[0] = (double) data.attribute(0).addStringValue(txtStr.toString());
	  if (m_OutputFilename)
	    newInst[1] = (double) data.attribute(1).addStringValue(subdirPath + File.separator + files[j]);
	  newInst[data.classIndex()] = (double) k;
	  data.add(new Instance(1.0, newInst));
          is.close();
	}
	catch (Exception e) {
	  System.err.println("failed to convert file: " + directoryPath + File.separator + subdirPath + File.separator + files[j]);
	}
      }
    }
    
    return data;
  }
  
  /**
   * TextDirectoryLoader is unable to process a data set incrementally.
   *
   * @param structure ignored
   * @return never returns without throwing an exception
   * @throws IOException always. TextDirectoryLoader is unable to process a data
   * set incrementally.
   */
  Instance getNextInstance(Instances structure) throws IOException {
    throw new IOException("TextDirectoryLoader can't read data sets incrementally.");
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 6768 $");
  }
  
};

/**
 * Main method.
 *
 * @param args should contain the name of an input file.
 */
void main(int argc, char* argv[]) {
  if (args.length > 0) {
    try {
      TextDirectoryLoader loader = new TextDirectoryLoader();
      loader.setOptions(args);
      System.out.println(loader.getDataSet());
    } 
    catch (Exception e) {
      e.printStackTrace();
    }
  } 
  else {
    System.err.println(
		       "\nUsage:\n" 
		       + "\tTextDirectoryLoader [options]\n"
		       + "\n"
		       + "Options:\n");

    Enumeration enm = ((OptionHandler) new TextDirectoryLoader()).listOptions();
    while (enm.hasMoreElements()) {
      Option option = (Option) enm.nextElement();
      System.err.println(option.synopsis());
      System.err.println(option.description());
    }
      
    System.err.println();
  }
}
