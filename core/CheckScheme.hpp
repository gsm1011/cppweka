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
#ifndef _CPP_WEKA_CHECKSCHEME_H_
#define _CPP_WEKA_CHECKSCHEME_H_

#include <vector>

// import java.util.Enumeration;
// import java.util.StringTokenizer;
// import java.util.Vector;

/**
 * Abstract general class for testing schemes in Weka. Derived classes are
 * also used for JUnit tests.
 *
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.4 $
 * @see TestInstances
 */
class CheckScheme : public Check {
  
  /** a class for postprocessing the test-data */
public:
  class PostProcessor : public RevisionHandler {
    
    /**
     * Provides a hook for derived classes to further modify the data. Currently,
     * the data is just passed through.
     * 
     * @param data	the data to process
     * @return		the processed data
     */
  public:
    inline Instances process(Instances data) {
      return data;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    inline string getRevision() {
      return RevisionUtils.extract("$Revision: 1.4 $");
    }
  };
  
  /** The number of instances in the datasets */
protected:
  int m_NumInstances = 20;
  
  /** the number of nominal attributes */
  int m_NumNominal = 2;
  
  /** the number of numeric attributes */
  int m_NumNumeric = 1;
  
  /** the number of string attributes */
  int m_Numstring = 1;
  
  /** the number of date attributes */
  int m_NumDate = 1;
  
  /** the number of relational attributes */
  int m_NumRelational = 1;
  
  /** the number of instances in relational attributes (applies also for bags
   * in multi-instance) */
  int m_NumInstancesRelational = 10;
  
  /** for generating string attributes/classes */
  String[] m_Words = TestInstances.DEFAULT_WORDS;
  
  /** for generating string attributes/classes */
  string m_WordSeparators = TestInstances.DEFAULT_SEPARATORS;
  
  /** for post-processing the data even further */
  PostProcessor m_PostProcessor = NULL;
  
  /** whether classpath problems occurred */
  bool m_ClasspathProblems = false;
  
public:
  /**
   * Returns an enumeration describing the available options.
   *
   * @return an enumeration of all the available options.
   */
    Enumeration listOptions();
  
  /**
   * Parses a given list of options. 
   *
   * @param options the list of options as an array of strings
   * @throws Exception if an option is not supported
   */
    void setOptions(String[] options); 
  
  /**
   * Gets the current settings of the CheckClassifier.
   *
   * @return an array of strings suitable for passing to setOptions
   */
    String[] getOptions(); 
  
  /**
   * sets the PostProcessor to use
   * 
   * @param value	the new PostProcessor
   * @see #m_PostProcessor
   */
 inline void setPostProcessor(PostProcessor value) {
    m_PostProcessor = value;
  }
  
  /**
   * returns the current PostProcessor, can be NULL
   * 
   * @return		the current PostProcessor
   */
  inline PostProcessor getPostProcessor() {
    return m_PostProcessor;
  }
  
  /**
   * returns TRUE if the classifier returned a "not in classpath" Exception
   * 
   * @return	true if CLASSPATH problems occurred
   */
  inline bool hasClasspathProblems() {
    return m_ClasspathProblems;
  }
  
  /**
   * Begin the tests, reporting results to System.out
   */
  abstract void doTests();
  
  /**
   * Sets the number of instances to use in the datasets (some classifiers
   * might require more instances).
   *
   * @param value the number of instances to use
   */
  inline void setNumInstances(int value) {
    m_NumInstances = value;
  }
  
  /**
   * Gets the current number of instances to use for the datasets.
   *
   * @return the number of instances
   */
  inline int getNumInstances() {
    return m_NumInstances;
  }
  
  /**
   * sets the number of nominal attributes
   * 
   * @param value	the number of nominal attributes
   */
 inline void setNumNominal(int value) {
    m_NumNominal = value;
  }
  
  /**
   * returns the current number of nominal attributes
   * 
   * @return 		the number of nominal attributes
   */
  inline int getNumNominal() {
    return m_NumNominal;
  }
  
  /**
   * sets the number of numeric attributes
   * 
   * @param value 	the number of numeric attributes
   */
  inline void setNumNumeric(int value) {
    m_NumNumeric = value;
  }
  
  /**
   * returns the current number of numeric attributes
   * 
   * @return 		the number of numeric attributes
   */
  inline int getNumNumeric() {
    return m_NumNumeric;
  }
  
  /**
   * sets the number of string attributes
   * 
   * @param value 	the number of string attributes
   */
  inline void setNumString(int value) {
    m_Numstring = value;
  }
  
  /**
   * returns the current number of string attributes
   * 
   * @return 		the number of string attributes
   */
  inline int getNumString() {
    return m_NumString;
  }
  
  /**
   * sets the number of data attributes
   * 
   * @param value	the number of date attributes
   */
  inline void setNumDate(int value) {
    m_NumDate = value;
  }
  
  /**
   * returns the current number of date attributes
   * 
   * @return		the number of date attributes
   */
  inline int getNumDate() {
    return m_NumDate;
  }
  
  /**
   * sets the number of relational attributes
   * 
   * @param value	the number of relational attributes
   */
  inline void setNumRelational(int value) {
    m_NumRelational = value;
  }
  
  /**
   * returns the current number of relational attributes
   * 
   * @return		the number of relational attributes
   */
  inline int getNumRelational() {
    return m_NumRelational;
  }
  
  /**
   * sets the number of instances in relational/bag attributes to produce
   * 
   * @param value	the number of instances
   */
  inline void setNumInstancesRelational(int value) {
    m_NumInstancesRelational = value;
  }
  
  /**
   * returns the current number of instances in relational/bag attributes to produce
   * 
   * @return		the number of instances
   */
  inline int getNumInstancesRelational() {
    return m_NumInstancesRelational;
  }

  /**
   * turns the comma-separated list into an array
   * 
   * @param value	the list to process
   * @return		the list as array
   */
protected:
    static String[] listToArray(string value); 
  
  /**
   * turns the array into a comma-separated list
   * 
   * @param value	the array to process
   * @return		the array as list
   */
    static string arrayToList(String[] value);
  
public:
  /**
   * returns a string representation of the attribute type
   * 
   * @param type	the attribute type to get a string rerpresentation for
   * @return		the string representation
   */
    static string attributeTypeToString(int type);
  
  /**
   * Sets the comma-separated list of words to use for generating strings. The
   * list must contain at least 2 words, otherwise an exception will be thrown.
   * 
   * @param value			the list of words
   * @throws IllegalArgumentException	if not at least 2 words are provided
   */
    void setWords(string value);
  
  /**
   * returns the words used for assembling strings in a comma-separated list.
   * 
   * @return		the words as comma-separated list
   */
  inline string getWords() {
    return arrayToList(m_Words);
  }

  /**
   * sets the word separators (chars) to use for assembling strings.
   * 
   * @param value	the characters to use as separators
   */
  inline void setWordSeparators(string value) {
    m_WordSeparators = value;
  }
  
  /**
   * returns the word separators (chars) to use for assembling strings.
   * 
   * @return		the current separators
   */
  inline string getWordSeparators() {
    return m_WordSeparators;
  }
  
  /**
   * Compare two datasets to see if they differ.
   *
   * @param data1 one set of instances
   * @param data2 the other set of instances
   * @throws Exception if the datasets differ
   */
protected:
    void compareDatasets(Instances data1, Instances data2); 
  
  /**
   * Add missing values to a dataset.
   *
   * @param data the instances to add missing values to
   * @param level the level of missing values to add (if positive, this
   * is the probability that a value will be set to missing, if negative
   * all but one value will be set to missing (not yet implemented))
   * @param predictorMissing if true, predictor attributes will be modified
   * @param classMissing if true, the class attribute will be modified
   */
  void addMissing(Instances data, int level,
		  bool predictorMissing, bool classMissing);
  
  /**
   * Provides a hook for derived classes to further modify the data. 
   * 
   * @param data	the data to process
   * @return		the processed data
   * @see #m_PostProcessor
   */
    Instances process(Instances data);
};
