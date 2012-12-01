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
 *    ArffSaver.cpp
 *    Copyright (C) 2004 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.converters;

// import weka.core.Capabilities;
// import weka.core.Instance;
// import weka.core.Instances;
// import weka.core.RevisionUtils;
// import weka.core.Capabilities.Capability;

// import java.io.IOException;
// import java.io.PrintWriter;

/**
 * Writes to a destination in arff text format. <p/>
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
 <!-- options-end -->
 *
 * @author Stefan Mutter (mutter@cs.waikato.ac.nz)
 * @version $Revision: 1.8 $
 * @see Saver
 */
class ArffSaver : public AbstractFileSaver, public BatchConverter, public IncrementalConverter {
public: 
  /** for serialization */
  const static long serialVersionUID = 2223634248900042228L;    
  
  /** Constructor */  
  ArffSaver(){
  
      resetOptions();
  }
   
   
  /**
   * Returns a string describing this Saver
   * @return a description of the Saver suitable for
   * displaying in the explorer/experimenter gui
   */
  string globalInfo() {
    return "Writes to a destination that is in arff (attribute relation file format) "
      +"format. ";
  }

  
  /**
   * Returns a description of the file type.
   *
   * @return a short file description
   */
  string getFileDescription() {
    return "Arff data files";
  }

  /**
   * Resets the Saver 
   */
  void resetOptions() {

    super.resetOptions();
    setFileExtension(".arff");
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
    result.enableAllAttributes();
    result.enable(Capability.MISSING_VALUES);
    
    // class
    result.enableAllClasses();
    result.enable(Capability.MISSING_CLASS_VALUES);
    result.enable(Capability.NO_CLASS);
    
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
      
      if(getRetrieval() == BATCH || getRetrieval() == NONE)
          throw new IOException("Batch and incremental saving cannot be mixed.");
      if(getWriter() != NULL)
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
          //write header
          Instances header = new Instances(structure,0);
          if(retrieveFile() == NULL || outW == NULL)
	    cout << header.toString() << endl
          else{
              outW.print(header.toString());
              outW.print("\n");
              outW.flush();
          }
          writeMode = getWriteMode();
      }
      if(writeMode == WRITE){
          if(structure == NULL)
              throw new IOException("No instances information available.");
          if(inst != NULL){
          //write instance 
              if(retrieveFile() == NULL || outW == NULL)
                cout << inst << endl;
              else{
                outW.println(inst);
                m_incrementalCounter++;
                //flush every 100 instances
                if(m_incrementalCounter > 100){
                    m_incrementalCounter = 0;
                    outW.flush();
                }
              }
          }
          else{
          //close
              if(outW != NULL){
                outW.flush();
                outW.close();
              }
              m_incrementalCounter = 0;
              resetStructure();
              outW = NULL;
              resetWriter();
          }
      }
  }
  
  /** Writes a Batch of instances
   * @throws IOException throws IOException if saving in batch mode is not possible
   */
  void writeBatch() throws IOException {
  
      if(getInstances() == NULL)
          throw new IOException("No instances to save");
      if(getRetrieval() == INCREMENTAL)
          throw new IOException("Batch and incremental saving cannot be mixed.");
      setRetrieval(BATCH);
      setWriteMode(WRITE);
      if(retrieveFile() == NULL && getWriter() == NULL){
	cout << getInstances().toString() << endl ;
	setWriteMode(WAIT);
	return;
      }
      PrintWriter outW = new PrintWriter(getWriter());
      outW.print((getInstances()).toString());
      outW.flush();
      outW.close();
      setWriteMode(WAIT);
      outW = NULL;
      resetWriter();
      setWriteMode(CANCEL);
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.8 $");
  }

  /**
   * Main method.
   *
   * @param args should contain the options of a Saver.
   */
  static void main(String[] args) {
    runFileSaver(new ArffSaver(), args);
  }
}
