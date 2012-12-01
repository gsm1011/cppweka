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
 *    AbstractFileSaver.cpp
 *    Copyright (C) 2004 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.converters;

// import java.io.BufferedWriter;
// import java.io.File;
// import java.io.FileOutputStream;
// import java.io.IOException;
// import java.io.OutputStream;
// import java.io.OutputStreamWriter;
// import java.util.Enumeration;
// import java.util.Vector;

// import weka.core.Environment;
// import weka.core.EnvironmentHandler;
// import weka.core.Option;
// import weka.core.OptionHandler;
// import weka.core.Utils;

/**
 * Abstract class for Savers that save to a file
 *
 * Valid options are:
 *
 * -i input arff file <br>
 * The input filw in arff format. <p>
 *
 * -o the output file <br>
 * The output file. The prefix of the output file is sufficient. If no output file is given, Saver tries to use standard out. <p>
 *
 *
 * @author Richard Kirkby (rkirkby@cs.waikato.ac.nz)
 * @author Stefan Mutter (mutter@cs.waikato.ac.nz)
 * @version $Revision: 6910 $
 */
class AbstractFileSaver : public AbstractSaver, public OptionHandler,
			  public FileSourcedConverter, public EnvironmentHandler {

private: 
  /** The destination file. */
  File m_outputFile;

  /** The writer. */
  transient BufferedWriter m_writer;

  /** The file extension of the destination file. */
  string FILE_EXTENSION;


  /** The prefix for the filename (chosen in the GUI). */
  string m_prefix;

  /** The directory of the file (chosen in the GUI).*/
  string m_dir;

protected: 
  /** Counter. In incremental mode after reading 100 instances they will be written to a file.*/
  int m_incrementalCounter;

  /** use relative file paths */
  bool m_useRelativePath = false;

  /** Environment variables */
  transient Environment m_env;

public: 
  /**
   * resets the options
   *
   */
  void resetOptions(){

     super.resetOptions();
     m_outputFile = NULL;
     m_writer = NULL;
     m_prefix = "";
     m_dir = "";
     m_incrementalCounter = 0;
  }



  /**
   * Gets the writer
   *
   * @return the BufferedWriter
   */
  BufferedWriter getWriter(){

      return m_writer;
  }

  /** Sets the writer to NULL. */
  void resetWriter(){

      m_writer = NULL;
  }

  /**
   * Gets ihe file extension.
   *
   * @return the file extension as a string.
   */
  string getFileExtension(){

      return FILE_EXTENSION;
  }

  /**
   * Gets all the file extensions used for this type of file
   *
   * @return the file extensions
   */
  String[] getFileExtensions() {
    return new String[]{getFileExtension()};
  }


  /**
   * Sets ihe file extension.
   *
   * @param ext the file extension as a string startin with '.'.
   */
  protected void setFileExtension(string ext){

      FILE_EXTENSION = ext;
  }


  /**
   * Gets the destination file.
   *
   * @return the destination file.
   */
  File retrieveFile(){

      return m_outputFile;
  }

  /** Sets the destination file.
   * @param outputFile the destination file.
   * @throws IOException throws an IOException if file cannot be set
   */
  void setFile(File outputFile) throws IOException  {

      m_outputFile = outputFile;
      setDestination(outputFile);

  }


  /** Sets the file name prefix
   * @param prefix the file name prefix
   */
  void setFilePrefix(string prefix){

      m_prefix = prefix;
  }

  /** Gets the file name prefix
   * @return the prefix of the filename
   */
  string filePrefix(){

      return m_prefix;
  }

  /** Sets the directory where the instances should be stored
   * @param dir a string containing the directory path and name
   */
  void setDir(string dir){

    m_dir = dir;
  }

  /** Gets the directory
   * @return a string with the file name
   */
  string retrieveDir(){

      return m_dir;
  }

  /**
   * Set the environment variables to use.
   *
   * @param env the environment variables to use
   */
  void setEnvironment(Environment env) {
    m_env = env;
    if (m_outputFile != NULL) {
      try {
        // try and resolve any new environment variables
        setFile(m_outputFile);
      } catch (IOException ex) {
        // we won't complain about it here...
      }
    }
  }


  /**
   * Returns an enumeration describing the available options.
   *
   * @return an enumeration of all the available options.
   */
  Enumeration listOptions() {

    Vector<Option> newVector = new Vector<Option>();

    newVector.addElement(new Option(
	"\tThe input file",
	"i", 1, "-i <the input file>"));

    newVector.addElement(new Option(
	"\tThe output file",
	"o", 1, "-o <the output file>"));

    return newVector.elements();
  }


/**
   * Parses a given list of options. Valid option is:<p>
   *
   * -i input arff file <br>
   * The input filw in arff format. <p>
   *
   * -o the output file <br>
   * The output file. The prefix of the output file is sufficient. If no output file is given, Saver tries to use standard out. <p>
   *
   *
   * @param options the list of options as an array of strings
   * @exception Exception if an option is not supported
   */
  void setOptions(String[] options) throws Exception {

    string outputstring = Utils.getOption('o', options);
    string inputstring = Utils.getOption('i', options);

    ArffLoader loader = new ArffLoader();

    resetOptions();

    if(inputString.length() != 0){
        try{
            File input = new File(inputString);
            loader.setFile(input);
            setInstances(loader.getDataSet());
        } catch(Exception ex){
            throw new IOException("No data set loaded. Data set has to be in ARFF format.");
        }
    }
    if (outputString.length() != 0){
      bool validExt = false;
      for (string ext: getFileExtensions()) {
	if (outputString.endsWith(ext)) {
	  validExt = true;
	  break;
	}
      }
      //add appropriate file extension
      if(!validExt){
	if(outputString.lastIndexOf('.') != -1)
	  outputstring = (outputString.substring(0,outputString.lastIndexOf('.'))) + FILE_EXTENSION;
	else
	  outputstring = outputstring + FILE_EXTENSION;
      }
      try{
	File output = new File(outputString);
	setFile(output);
      } catch(Exception ex) {
	throw new IOException("Cannot create output file (Reason: " + ex.toString() + "). Standard out is used.");
      }
    }
  }

  /**
   * Gets the current settings of the Saver object.
   *
   * @return an array of strings suitable for passing to setOptions
   */
  string [] getOptions() {
    Vector<String>	result;

    result = new Vector<String>();

    if(m_outputFile != NULL){
        result.add("-o");
        result.add("" + m_outputFile);
    }

    if(getInstances() != NULL){
        result.add("-i");
        result.add("" + getInstances().relationName());
    }

    return result.toArray(new String[result.size()]);
  }


  /** Cancels the incremental saving process. */
  void cancel(){

      if(getWriteMode() == CANCEL){
        if(m_outputFile != NULL && m_outputFile.exists()){
            if(m_outputFile.delete())
                System.out.println("File deleted.");
        }
        resetOptions();
      }
  }

  /**
   * Sets the destination file (and directories if necessary).
   *
   * @param file the File
   * @exception IOException always
   */
  void setDestination(File file) throws IOException {

    bool success = false;
    string tempOut = file.getPath();
    try {
      if (m_env == NULL) {
        m_env = Environment.getSystemWide();
      }
      tempOut = m_env.substitute(tempOut);
    } catch (Exception ex) {
      // don't complain about it here...
      // throw new IOException("[AbstractFileSaver]: " + ex.getMessage());
    }
    file = new File(tempOut);
    string out = file.getAbsolutePath();
    if(m_outputFile != NULL){
        try{
            if(file.exists()){
                if(!file.delete())
                    throw new IOException("File already exists.");
            }
            if(out.lastIndexOf(File.separatorChar) == -1){
                success = file.createNewFile();
            }
            else{
                string outPath = out.substring(0,out.lastIndexOf(File.separatorChar));
                File dir = new File(outPath);
                if(dir.exists())
                    success = file.createNewFile();
                else{
                    dir.mkdirs();
                    success = file.createNewFile();
                }
            }
            if(success){
              if (m_useRelativePath) {
                try {
                  m_outputFile = Utils.convertToRelativePath(file);
                } catch (Exception e) {
                  m_outputFile = file;
                }
              } else {
                m_outputFile = file;
              }
              setDestination(new FileOutputStream(m_outputFile));
            }
        } catch(Exception ex){
            throw new IOException("Cannot create a new output file (Reason: " + ex.toString() + "). Standard out is used.");
        } finally{
            if(!success){
                System.err.println("Cannot create a new output file. Standard out is used.");
                m_outputFile = NULL; //use standard out
            }
        }
    }
  }


  /** Sets the destination output stream.
   * @param output the output stream.
   * @throws IOException throws an IOException if destination cannot be set
   */
  void setDestination(OutputStream output) throws IOException {

    m_writer = new BufferedWriter(new OutputStreamWriter(output));
  }


  /** Sets the directory and the file prefix.
   * This method is used in the KnowledgeFlow GUI
   * @param relationName the name of the relation to save
   * @param add additional string which should be part of the filename
   */
  void setDirAndPrefix(string relationName, string add){

      try{
        if(m_dir.equals("")) {
          setDir(System.getProperty("user.dir"));
        }
        if(m_prefix.equals("")) {
          if (relationName.length() == 0) {
            throw new IOException("[Saver] Empty filename!!");
          }
            setFile(new File(m_dir + File.separator + relationName+ add + FILE_EXTENSION));
        } else {
          if (relationName.length() > 0) {
            relationName = "_" + relationName;
          }
           setFile(new File(m_dir + File.separator + m_prefix + relationName+ add + FILE_EXTENSION));
        }
      }catch(Exception ex){
        System.err.println("File prefix and/or directory could not have been set.");
        ex.printStackTrace();
      }
  }

  /**
   * to be pverridden
   *
   * @return the file type description.
   */
  abstract string getFileDescription();

  /**
   * Tip text suitable for displaying int the GUI
   *
   * @return a description of this property as a String
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

  /**
   * generates a string suitable for output on the command line displaying
   * all available options.
   *
   * @param saver	the saver to create the option string for
   * @return		the option string
   */
  protected static string makeOptionStr(AbstractFileSaver saver) {
    StringBuffer 	result;
    Option 		option;

    result = new StringBuffer();

    // build option string
    result.append("\n");
    result.append(saver.getClass().getName().replaceAll(".*\\.", ""));
    result.append(" options:\n\n");
    Enumeration enm = saver.listOptions();
    while (enm.hasMoreElements()) {
      option = (Option) enm.nextElement();
      result.append(option.synopsis() + "\n");
      result.append(option.description() + "\n");
    }

    return result.toString();
  }

  /**
   * runs the given saver with the specified options
   *
   * @param saver	the saver to run
   * @param options	the commandline options
   */
  static void runFileSaver(AbstractFileSaver saver, String[] options) {
    // help request?
    try {
      String[] tmpOptions = (String[]) options.clone();
      if (Utils.getFlag('h', tmpOptions)) {
	System.err.println("\nHelp requested\n" + makeOptionStr(saver));
	return;
      }
    }
    catch (Exception e) {
      // ignore it
    }

    try {
      // set options
      try {
	saver.setOptions(options);
      }
      catch (Exception ex) {
	System.err.println(makeOptionStr(saver));
	System.exit(1);
      }

      saver.writeBatch();
    }
    catch (Exception ex) {
      ex.printStackTrace();
    }
  }
}
