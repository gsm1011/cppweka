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
 *    C45Saver.cpp
 *    Copyright (C) 2004 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.converters;

// import weka.core.Attribute;
// import weka.core.Capabilities;
// import weka.core.FastVector;
// import weka.core.Instance;
// import weka.core.Instances;
// import weka.core.Option;
// import weka.core.OptionHandler;
// import weka.core.RevisionUtils;
// import weka.core.Utils;
// import weka.core.Capabilities.Capability;

// import java.io.File;
// import java.io.IOException;
// import java.io.PrintWriter;
// import java.util.Enumeration;

/**
   <!-- globalinfo-start -->
   * Writes to a destination that is in the format used by the C4.5 algorithm.<br/>
   * Therefore it outputs a names and a data file.
   * <p/>
   <!-- globalinfo-end -->
   * 
   <!-- options-start -->
   * Valid options are: <p/>
   * 
   * <pre> -i &lt;the input file&gt;
   * The input file</pre>
   * 
   * <pre> -o &lt;the output file&gt;
   * The output file</pre>
   * 
   * <pre> -c &lt;the class index&gt;
   * The class index</pre>
   * 
   <!-- options-end -->
   *
   * @author Stefan Mutter (mutter@cs.waikato.ac.nz)
   * @version $Revision: 1.7 $
   * @see Saver
   */
class C45Saver : public AbstractFileSaver, public BatchConverter,
		 public IncrementalConverter, public OptionHandler {

  /** for serialization */
  // static final long serialVersionUID = -821428878384253377L;
public: 
  /** Constructor */  
  C45Saver(){
  
    resetOptions();
  }
   
  /**
   * Returns a string describing this Saver
   * @return a description of the Saver suitable for
   * displaying in the explorer/experimenter gui
   */
  string globalInfo() {
    return "Writes to a destination that is in the format used by the C4.5 algorithm.\nTherefore it outputs a names and a data file.";
  }

  
  /**
   * Returns a description of the file type.
   *
   * @return a short file description
   */
  string getFileDescription() {
    return "C4.5 file format";
  }

  /**
   * Resets the Saver 
   */
  void resetOptions() {

    super.resetOptions();
    setFileExtension(".names");
  }

  /** 
   * Returns the Capabilities of this saver.
   *
   * @return            the capabilities of this object
   * @see               Capabilities
   */
  Capabilities getCapabilities() {
    Capabilities result = super.getCapabilities();
    
    // attributes
    result.enable(Capability.NOMINAL_ATTRIBUTES);
    result.enable(Capability.NUMERIC_ATTRIBUTES);
    result.enable(Capability.DATE_ATTRIBUTES);
    result.enable(Capability.MISSING_VALUES);
    
    // class
    result.enable(Capability.NOMINAL_CLASS);
    result.enable(Capability.NUMERIC_CLASS);
    result.enable(Capability.DATE_CLASS);
    result.enable(Capability.MISSING_CLASS_VALUES);
    
    return result;
  }

  /** Saves an instances incrementally. Structure has to be set by using the
   * setStructure() method or setInstances() method.
   * @param inst the instance to save
   * @throws IOException throws IOEXception if an instance cannot be saved incrementally.
   */  
  void writeIncremental(Instance inst) throws IOException{
  
    int writeMode = getWriteMode();
    Instances structure = getInstances();
    PrintWriter outW = NULL;
      
    if(structure != NULL){
      if(structure.classIndex() == -1){
	structure.setClassIndex(structure.numAttributes()-1);
	System.err.println("No class specified. Last attribute is used as class attribute.");
      }
      if(structure.attribute(structure.classIndex()).isNumeric())
	throw new IOException("To save in C4.5 format the class attribute cannot be numeric.");
    }
    if(getRetrieval() == BATCH || getRetrieval() == NONE)
      throw new IOException("Batch and incremental saving cannot be mixed.");
    if(retrieveFile() == NULL || getWriter() == NULL){
      throw new IOException("C4.5 format requires two files. Therefore no output to standard out can be generated.\nPlease specifiy output files using the -o option.");
    }
      
      
    outW = new PrintWriter(getWriter());
          
    if(writeMode == WAIT){
      if(structure == NULL){
	setWriteMode(CANCEL);
	if(inst != NULL)
	  System.err.println("Structure(Header Information) has to be set in advance");
      }
      else
	setWriteMode(STRUCTURE_READY);
      writeMode = getWriteMode();
    }
    if(writeMode == CANCEL){
      if(outW != NULL)
	outW.close();
      cancel();
    }
    if(writeMode == STRUCTURE_READY){
      setWriteMode(WRITE);
      //write header: here names file
      for (int i = 0; i < structure.attribute(structure.classIndex()).numValues(); i++) {
	outW.write(structure.attribute(structure.classIndex()).value(i));
	if (i < structure.attribute(structure.classIndex()).numValues()-1) {
	  outW.write(",");
	} else {
	  outW.write(".\n");
	}
      }
      for (int i = 0; i < structure.numAttributes(); i++) {
	if (i != structure.classIndex()) {
	  outW.write(structure.attribute(i).name()+": ");
	  if (structure.attribute(i).isNumeric() || structure.attribute(i).isDate()) {
	    outW.write("continuous.\n");
	  } else {
	    Attribute temp = structure.attribute(i);
	    for (int j = 0; j < temp.numValues(); j++) {
	      outW.write(temp.value(j));
	      if (j < temp.numValues()-1) {
		outW.write(",");
	      } else {
		outW.write(".\n");
	      }
	    }
	  }
	}
      }
      outW.flush();
      outW.close();
          
      writeMode = getWriteMode();
          
      string out = retrieveFile().getAbsolutePath();
      setFileExtension(".data");
      out = out.substring(0, out.lastIndexOf('.')) + getFileExtension();
      File namesFile = new File(out);
      try{
	setFile(namesFile);
      } catch(Exception ex){
	throw new IOException("Cannot create data file, only names file created.");
      }
      if(retrieveFile() == NULL || getWriter() == NULL){
	throw new IOException("Cannot create data file, only names file created.");
      }
      outW = new PrintWriter(getWriter());
    }
    if(writeMode == WRITE){
      if(structure == NULL)
	throw new IOException("No instances information available.");
      if(inst != NULL){
	//write instance: here data file
	for(int j = 0; j < inst.numAttributes(); j++){
	  if(j != structure.classIndex()){
	    if (inst.isMissing(j)) {
	      outW.write("?,");
	    } else 
	      if (structure.attribute(j).isNominal() || 
		  structure.attribute(j).isString()) {
		outW.write(structure.attribute(j).value((int)inst.value(j))+",");
	      } else {
		outW.write(""+inst.value(j)+",");
	      }
	  }
	}
	// write the class value
	if (inst.isMissing(structure.classIndex())) {
	  outW.write("?");
	} 
	else {
	  outW.write(structure.attribute(structure.classIndex()).value((int)inst.value(structure.classIndex())));
	}
	outW.write("\n");
	//flushes every 100 instances
	m_incrementalCounter++;
	if(m_incrementalCounter > 100){
	  m_incrementalCounter = 0;
	  outW.flush();
	}
      }
      else{
	//close
	if(outW != NULL){
	  outW.flush();
	  outW.close();
	}
	setFileExtension(".names");
	m_incrementalCounter = 0;
	resetStructure();
	outW = NULL;
	resetWriter();
      }
    }
  }

  
  /** 
   * Writes a Batch of instances
   * @throws IOException throws IOException if saving in batch mode is not possible
   */
  void writeBatch() throws IOException {
      
    Instances instances = getInstances();
      
    if(instances == NULL)
      throw new IOException("No instances to save");
    if(instances.classIndex() == -1){
      instances.setClassIndex(instances.numAttributes()-1);
      System.err.println("No class specified. Last attribute is used as class attribute.");
    }
    if(instances.attribute(instances.classIndex()).isNumeric())
      throw new IOException("To save in C4.5 format the class attribute cannot be numeric.");
    if(getRetrieval() == INCREMENTAL)
      throw new IOException("Batch and incremental saving cannot be mixed.");
      
    setRetrieval(BATCH);
    if(retrieveFile() == NULL || getWriter() == NULL){
      throw new IOException("C4.5 format requires two files. Therefore no output to standard out can be generated.\nPlease specifiy output files using the -o option.");
    }
    setWriteMode(WRITE);
    //print names file
    setFileExtension(".names");
    PrintWriter outW = new PrintWriter(getWriter());
    for (int i = 0; i < instances.attribute(instances.classIndex()).numValues(); i++) {
      outW.write(instances.attribute(instances.classIndex()).value(i));
      if (i < instances.attribute(instances.classIndex()).numValues()-1) {
	outW.write(",");
      } else {
	outW.write(".\n");
      }
    }
    for (int i = 0; i < instances.numAttributes(); i++) {
      if (i != instances.classIndex()) {
	outW.write(instances.attribute(i).name()+": ");
	if (instances.attribute(i).isNumeric() || instances.attribute(i).isDate()) {
	  outW.write("continuous.\n");
	} else {
	  Attribute temp = instances.attribute(i);
	  for (int j = 0; j < temp.numValues(); j++) {
	    outW.write(temp.value(j));
	    if (j < temp.numValues()-1) {
	      outW.write(",");
	    } else {
	      outW.write(".\n");
	    }
	  }
	}
      }
    }
    outW.flush();
    outW.close();
      
    //print data file
    string out = retrieveFile().getAbsolutePath();
    setFileExtension(".data");
    out = out.substring(0, out.lastIndexOf('.')) + getFileExtension();
    File namesFile = new File(out);
    try{
      setFile(namesFile);
    } catch(Exception ex){
      throw new IOException("Cannot create data file, only names file created (Reason: " + ex.toString() + ").");
    }
    if(retrieveFile() == NULL || getWriter() == NULL){
      throw new IOException("Cannot create data file, only names file created.");
    }
    outW = new PrintWriter(getWriter());
    // print data file
    for (int i = 0; i < instances.numInstances(); i++) {
      Instance temp = instances.instance(i);
      for(int j = 0; j < temp.numAttributes(); j++){
	if(j != instances.classIndex()){
	  if (temp.isMissing(j)) {
	    outW.write("?,");
	  } else if (instances.attribute(j).isNominal() || 
		     instances.attribute(j).isString()) {
	    outW.write(instances.attribute(j).value((int)temp.value(j))+",");
	  } else {
	    outW.write(""+temp.value(j)+",");
	  }
	}
      }
      // write the class value
      if (temp.isMissing(instances.classIndex())) {
	outW.write("?");
      } 
      else {
	outW.write(instances.attribute(instances.classIndex()).value((int)temp.value(instances.classIndex())));
      }
      outW.write("\n");
    }
    outW.flush();
    outW.close();
    setFileExtension(".names");
    setWriteMode(WAIT);
    outW = NULL;
    resetWriter();
    setWriteMode(CANCEL);
  }
  
  
  /**
   * Returns an enumeration describing the available options.
   *
   * @return an enumeration of all the available options.
   */
  Enumeration listOptions() {
    FastVector result = new FastVector();

    Enumeration en = super.listOptions();
    while (en.hasMoreElements())
      result.addElement(en.nextElement());

    result.addElement(new Option(
				 "The class index", 
				 "c", 1, "-c <the class index>"));
    
    return result.elements();
  }

 
  /**
   * Parses a given list of options. <p/>
   *
   <!-- options-start -->
   * Valid options are: <p/>
   * 
   * <pre> -i &lt;the input file&gt;
   * The input file</pre>
   * 
   * <pre> -o &lt;the output file&gt;
   * The output file</pre>
   * 
   * <pre> -c &lt;the class index&gt;
   * The class index</pre>
   * 
   <!-- options-end -->
   *
   * @param options the list of options as an array of strings
   * @throws Exception if an option is not supported 
   */
  void setOptions(String[] options) throws Exception {
    
    string outputstring = Utils.getOption('o', options);
    string inputstring = Utils.getOption('i', options);
    string indexstring = Utils.getOption('c', options);
    
    ArffLoader loader = new ArffLoader();
    
    resetOptions();

    // parse index
    int index = -1;
    if (indexString.length() != 0){
      if(indexString.equals("first"))
	index = 0;
      else {
	if (indexString.equals("last"))
	  index = -1;
	else
	  index = Integer.parseInt(indexString);
      }
    }
    
    if (inputString.length() != 0){
      try {
	File input = new File(inputString);
	loader.setFile(input);
	Instances inst = loader.getDataSet();
	if (index == -1)
	  inst.setClassIndex(inst.numAttributes() - 1);
	else
	  inst.setClassIndex(index);
	setInstances(inst);
      } catch(Exception ex){
	throw new IOException("No data set loaded. Data set has to be arff format (Reason: " + ex.toString() + ").");
      }
    }
    else
      throw new IOException("No data set to save.");

    if (outputString.length() != 0){ 
      //add appropriate file extension
      if (!outputString.endsWith(getFileExtension())){
	if (outputString.lastIndexOf('.') != -1)
	  outputstring = (outputString.substring(0,outputString.lastIndexOf('.'))) + getFileExtension();
	else
	  outputstring = outputstring + getFileExtension();
      }
      try {
	File output = new File(outputString);
	setFile(output);
      } catch(Exception ex){
	throw new IOException("Cannot create output file.");
      }
    }

    if (index == -1)
      index = getInstances().numAttributes() - 1;
    getInstances().setClassIndex(index);
  }

  /**
   * Gets the current settings of the C45Saver object.
   *
   * @return an array of strings suitable for passing to setOptions
   */
  string [] getOptions() {

    string [] options = new string [10];
    int current = 0;
    if(retrieveFile() != NULL){
      options[current++] = "-o"; options[current++] = "" + retrieveFile();
    }
    else{
      options[current++] = "-o"; options[current++] = "";
    }
    if(getInstances() != NULL){
      options[current++] = "-i"; options[current++] = "" + getInstances().relationName();
      options[current++] = "-c"; options[current++] = "" + getInstances().classIndex();
    }
    else{
      options[current++] = "-i"; options[current++] = "";
      options[current++] = "-c"; options[current++] = "";
    }
    while (current < options.length) {
      options[current++] = "";
    }
    return options;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.7 $");
  }
  
  /**
   * Main method.
   *
   * @param args should contain the options of a Saver.
   */
  static void main(String[] args) {
    runFileSaver(new C45Saver(), args);
  }
}
