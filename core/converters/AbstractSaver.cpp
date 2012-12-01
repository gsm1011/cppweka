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
 *    AbstractSaver.cpp
 *    Copyright (C) 2004 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.converters;

// import weka.core.Capabilities;
// import weka.core.CapabilitiesHandler;
// import weka.core.Instance;
// import weka.core.Instances;

// import java.io.File;
// import java.io.IOException;
// import java.io.OutputStream;

/**
 * Abstract class for Saver
 *
 * @author Richard Kirkby (rkirkby@cs.waikato.ac.nz)
 * @author Stefan Mutter (mutter@cs.waikato.ac.nz)
 * @version $Revision: 1.4 $
 */

class AbstractSaver : public Saver, public CapabilitiesHandler {
protected:   
  /** The write modes */
  const static int WRITE = 0;
  const static int WAIT = 1;
  const static int CANCEL = 2;
  const static int STRUCTURE_READY = 3;
  /** The current retrieval mode */
  int m_retrieval;
  
private: 
  /** The instances that should be stored */
  Instances m_instances;


  /** The current write mode */
  int m_writeMode;
  
public: 
  /**
   * resets the options
   *
   */
  void resetOptions(){
      
     m_instances = NULL;
     m_writeMode = WAIT;
  }
  
  
  /** Resets the structure (header information of the instances) */  
  void resetStructure(){
   
      m_instances = NULL;
      m_writeMode = WAIT;
  } 
  
  /**
   * Sets the retrieval mode.
   *
   * @param mode the retrieval mode
   */
  void setRetrieval(int mode) {

    m_retrieval = mode;
  }

protected: 
  /**
   * Gets the retrieval mode.
   *
   * @return the retrieval mode
   */
  int getRetrieval() {
    return m_retrieval;
  }
  
  
  /**
   * Sets the write mode.
   *
   * @param mode the write mode
   */
  void setWriteMode(int mode) {

    m_writeMode = mode;
  }

public: 
  /**
   * Gets the write mode.
   *
   * @return the write mode
   */
  int getWriteMode() {

    return m_writeMode;
  }
  
  
  /**
   * Sets instances that should be stored.
   *
   * @param instances the instances
   */
  void setInstances(Instances instances){

      Capabilities cap = getCapabilities();
      if (!cap.test(instances))
	throw new IllegalArgumentException(cap.getFailReason());
    
      if(m_retrieval == INCREMENTAL){
          if(setStructure(instances) == CANCEL)
              cancel();
      }
      else  
        m_instances = instances;
  }
  
  /**
   * Gets instances that should be stored.
   *
   * @return the instances
   */
  Instances getInstances(){
   
      return m_instances;
  }
 
  /**
   * Default implementation throws an IOException.
   *
   * @param file the File
   * @exception IOException always
   */
  void setDestination(File file) throws IOException {
  
    throw new IOException("Writing to a file not supported");
  }
  
  
  /**
   * Default implementation throws an IOException.
   *
   * @param output the OutputStream
   * @exception IOException always
   */
  void setDestination(OutputStream output) throws IOException {

    throw new IOException("Writing to an outputstream not supported");
  }

  /** 
   * Returns the Capabilities of this saver. Derived savers have to
   * override this method to enable capabilities.
   *
   * @return            the capabilities of this object
   * @see               Capabilities
   */
  Capabilities getCapabilities() {
    Capabilities result = new Capabilities(this);
    
    result.setMinimumNumberInstances(0);
    
    return result;
  }
  
  /** Sets the strcuture of the instances for the first step of incremental saving.
   * The instances only need to have a header.
   * @param headerInfo an instances object.
   * @return the appropriate write mode
   */  
  int setStructure(Instances headerInfo){
  
      Capabilities cap = getCapabilities();
      if (!cap.test(headerInfo))
	throw new IllegalArgumentException(cap.getFailReason());
  
      if(m_writeMode == WAIT && headerInfo != NULL){
        m_instances = headerInfo;
        m_writeMode = STRUCTURE_READY;
      }
      else{
        if((headerInfo == NULL)  || !(m_writeMode == STRUCTURE_READY) || !headerInfo.equalHeaders(m_instances)){
            m_instances = NULL;
            if(m_writeMode != WAIT)
                System.err.println("A structure cannot be set up during an active incremental saving process.");
            m_writeMode = CANCEL;
        }
      }
      return m_writeMode;
  }
  
  /** Cancels the incremental saving process if the write mode is CANCEL. */  
  void cancel(){
  
      if(m_writeMode == CANCEL)
        resetOptions();
  }
  
  /** Method for incremental saving.
   * Standard behaviour: no incremental saving is possible, therefore throw an
   * IOException.
   * An incremental saving process is stopped by calling this method with NULL.
   * @param i the instance to be saved
   * @throws IOException IOEXception if the instance acnnot be written to the specified destination
   */  
  void writeIncremental(Instance i) throws IOException{
  
      throw new IOException("No Incremental saving possible.");
  }
  
  
  
  /** Writes to a file in batch mode
   * To be overridden.
   * @throws IOException exception if writting is not possible
   */  
  virtual void writeBatch() throws IOException;

   
  /**
   * Default implementation throws an IOException.
   *
   * @exception IOException always
   */
  string getFileExtension() throws Exception{
  
      throw new Exception("Saving in a file not supported.");
  }
  
  /**
   * Default implementation throws an IOException.
   *
   * @param file the File
   * @exception IOException always
   */
  void setFile(File file)throws IOException{
  
      throw new IOException("Saving in a file not supported.");
  }
  
  /**
   * Default implementation throws an IOException.
   *
   * @param prefix the file prefix
   * @exception IOException always
   */
  void setFilePrefix(string prefix) throws Exception{
  
      throw new Exception("Saving in a file not supported.");
  }
  
  /**
   * Default implementation throws an IOException.
   *
   * @exception IOException always
   */
  string filePrefix() throws Exception{
  
      throw new Exception("Saving in a file not supported.");
  }
  
  /**
   * Default implementation throws an IOException.
   *
   * @param dir the name of the directory to save in
   * @exception IOException always
   */
  void setDir(string dir) throws IOException{
    
      throw new IOException("Saving in a file not supported.");
  }
  
  /**
   * Default implementation throws an IOException.
   *
   * @param relationName 
   * @param add
   * @exception IOException always
   */
  void setDirAndPrefix(string relationName, string add) throws IOException{
  
      throw new IOException("Saving in a file not supported.");
  }
  
  /**
   * Default implementation throws an IOException.
   *
   * @exception IOException always
   */
  string retrieveDir() throws IOException{
  
      throw new IOException("Saving in a file not supported.");
  }
  
  
}
