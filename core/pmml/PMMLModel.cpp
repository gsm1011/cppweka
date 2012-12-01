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
 *    PMMLModel.java
 *    Copyright (C) 2008 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.pmml;

// import org.w3c.dom.Document;

// import weka.gui.Logger;

/**
 * Interface for all PMML models
 *
 * @author Mark Hall (mhall{[at]}pentaho{[dot]}com)
 * @version $Revision: 5562 $
 */
class PMMLModel {
public:
  /**
   * Set the version of the PMML.
   *
   * @param doc the Document encapsulating the pmml
   */
  virtual void setPMMLVersion(Document doc) = 0;
  
  /**
   * Get the version of PMML used to encode this model.
   *
   * @return the version as a String
   */
  virtual string getPMMLVersion() = 0;
  
  /**
   * Set the name of the application (if specified) that created this.
   * model
   * 
   * @param doc the Document encapsulating the pmml
   */
  virtual void setCreatorApplication(Document doc) = 0;
  
  /**
   * Get the name of the application that created this model.
   * 
   * @return the name of the creating application or null
   * if not specified in the pmml.
   */
  virtual string getCreatorApplication() = 0;

  /**
   * Get the mining schema.
   *
   * @return the mining schema
   */
  virtual MiningSchema getMiningSchema() = 0;
  
  /**
   * Set a logger to use.
   * 
   * @param log the logger to use
   */
  virtual void setLog(Logger log) = 0;
  
  /**
   * Get the logger.
   * 
   * @return the logger (or null if none is being used)
   */
  virtual Logger getLog() = 0;
};
