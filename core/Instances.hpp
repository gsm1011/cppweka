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
 *    Instances.cpp
 *    Copyright (C) 1999 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import weka.core.converters.ArffLoader.ArffReader;
// import weka.core.converters.ConverterUtils.DataSource;

// import java.io.FileReader;
// import java.io.IOException;
// import java.io.Reader;
// import java.io.Serializable;
// import java.util.Enumeration;
// import java.util.HashSet;
// import java.util.Random;
#include <iostream>
#include <string>
#include <vector>
#include "RevisionHandler.hpp"
#include "FastVector.hpp"
#include "Instances.hpp"
#include "Instance.hpp"

using namespace std;

/**
 * Class for handling an ordered set of weighted instances. <p>
 *
 * Typical usage: <p>
 * <pre>
 * import weka.core.converters.ConverterUtils.DataSource;
 * ...
 *
 * // Read all the instances in the file (ARFF, CSV, XRFF, ...)
 * DataSource source = new DataSource(filename);
 * Instances instances = source.getDataSet();
 *
 * // Make the last attribute be the class
 * instances.setClassIndex(instances.numAttributes() - 1);
 *
 * // Print header and instances.
 * System.out.println("\nDataset:\n");
 * System.out.println(instances);
 *
 * ...
 * </pre><p>
 *
 * All methods that change a set of instances are safe, ie. a change
 * of a set of instances does not affect any other sets of
 * instances. All methods that change a datasets's attribute
 * information clone the dataset before it is changed.
 *
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @author Len Trigg (trigg@cs.waikato.ac.nz)
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 6996 $
 */
class Instances : public Serializable, public RevisionHandler {

  /** for serialization */
  // static final long serialVersionUID = -19412345060742748L;
public:
  /** The filename extension that should be used for arff files */
  const static string FILE_EXTENSION = ".arff";

  /** The filename extension that should be used for bin. serialized instances files */
  const static string SERIALIZED_OBJ_FILE_EXTENSION = ".bsi";

  /** The keyword used to denote the start of an arff header */
  const static string ARFF_RELATION = "@relation";

  /** The keyword used to denote the start of the arff data section */
  const static string ARFF_DATA = "@data";

  /** The dataset's name. */
protected:
  /*@spec_public non_NULL@*/ string m_RelationName;

  /** The attribute information. */
  /*@spec_public non_NULL@*/ FastVector m_Attributes;
  /*  public invariant (\forall int i; 0 <= i && i < m_Attributes.size();
                    m_Attributes.elementAt(i) != NULL);
  */

  /** The instances. */
  /*@spec_public non_NULL@*/ FastVector m_Instances;

  /** The class attribute's index */
  int m_ClassIndex;
  //@ protected invariant classIndex() == m_ClassIndex;

  /** The lines read so far in case of incremental loading. Since the
   * StreamTokenizer will be re-initialized with every instance that is read,
   * we have to keep track of the number of lines read so far.
   * @see #readInstance(Reader) */
  int m_Lines = 0;

private:
  /** used in randomizeAttribute and undoRandomizeAttribute to store/restore
   * the index of attribute that was last shuffled, and it's original values
   */
  int attIdx4Randomization = -1;
  double[] attIdxOrigValues;

public:
  /**
   * Reads an ARFF file from a reader, and assigns a weight of
   * one to each instance. Lets the index of the class
   * attribute be undefined (negative).
   *
   * @param reader the reader
   * @throws IOException if the ARFF file is not read
   * successfully
   */
  Instances(/*@non_NULL@*/Reader reader) throws IOException {
    ArffReader arff = new ArffReader(reader);
    Instances dataset = arff.getData();
    initialize(dataset, dataset.numInstances());
    dataset.copyInstances(0, this, dataset.numInstances());
    compactify();
  }

  /**
   * Reads the header of an ARFF file from a reader and
   * reserves space for the given number of instances. Lets
   * the class index be undefined (negative).
   *
   * @param reader the reader
   * @param capacity the capacity
   * @throws IllegalArgumentException if the header is not read successfully
   * or the capacity is negative.
   * @throws IOException if there is a problem with the reader.
   * @deprecated instead of using this method in conjunction with the
   * <code>readInstance(Reader)</code> method, one should use the
   * <code>ArffLoader</code> or <code>DataSource</code> class instead.
   * @see weka.core.converters.ArffLoader
   * @see weka.core.converters.ConverterUtils.DataSource
   */
  //@ requires capacity >= 0;
  //@ ensures classIndex() == -1;
  /*@Deprecated*/ Instances(/*@non_NULL@*/Reader reader, int capacity)
    throw(IOException) {

    ArffReader arff = new ArffReader(reader, 0);
    Instances header = arff.getStructure();
    initialize(header, capacity);
    m_Lines = arff.getLineNo();
  }

  /**
   * Constructor copying all instances and references to
   * the header information from the given set of instances.
   *
   * @param dataset the set to be copied
   */
  Instances(/*@non_NULL@*/Instances dataset) {

    this(dataset, dataset.numInstances());

    dataset.copyInstances(0, this, dataset.numInstances());
  }

  /**
   * Constructor creating an empty set of instances. Copies references
   * to the header information from the given set of instances. Sets
   * the capacity of the set of instances to 0 if its negative.
   *
   * @param dataset the instances from which the header
   * information is to be taken
   * @param capacity the capacity of the new dataset
   */
  Instances(/*@non_NULL@*/Instances dataset, int capacity) {
    initialize(dataset, capacity);
  }

  /**
   * initializes with the header information of the given dataset and sets
   * the capacity of the set of instances.
   *
   * @param dataset the dataset to use as template
   * @param capacity the number of rows to reserve
   */
protected:
  void initialize(Instances dataset, int capacity) {
    if (capacity < 0)
      capacity = 0;

    // Strings only have to be "shallow" copied because
    // they can't be modified.
    m_ClassIndex   = dataset.m_ClassIndex;
    m_RelationName = dataset.m_RelationName;
    m_Attributes   = dataset.m_Attributes;
    m_Instances    = new FastVector(capacity);
  }
public:
  /**
   * Creates a new set of instances by copying a
   * subset of another set.
   *
   * @param source the set of instances from which a subset
   * is to be created
   * @param first the index of the first instance to be copied
   * @param toCopy the number of instances to be copied
   * @throws IllegalArgumentException if first and toCopy are out of range
   */
  //@ requires 0 <= first;
  //@ requires 0 <= toCopy;
  //@ requires first + toCopy <= source.numInstances();
  Instances(/*@non_NULL@*/Instances source, int first, int toCopy) {

    this(source, toCopy);

    if ((first < 0) || ((first + toCopy) > source.numInstances())) {
      throw new IllegalArgumentException("Parameters first and/or toCopy out "+
                                         "of range");
    }
    source.copyInstances(first, this, toCopy);
  }

  /**
   * Creates an empty set of instances. Uses the given
   * attribute information. Sets the capacity of the set of
   * instances to 0 if its negative. Given attribute information
   * must not be changed after this constructor has been used.
   *
   * @param name the name of the relation
   * @param attInfo the attribute information
   * @param capacity the capacity of the set
   */
  Instances(/*@non_NULL@*/string name,
	    /*@non_NULL@*/FastVector attInfo, int capacity);

  /**
   * Create a copy of the structure if the data has string or
   * relational attributes, "cleanses" string types (i.e. doesn't
   * contain references to the strings seen in the past) and all
   * relational attributes.
   *
   * @return a copy of the instance structure.
   */
  Instances stringFreeStructure();

  /**
   * Adds one instance to the end of the set.
   * Shallow copies instance before it is added. Increases the
   * size of the dataset if it is not large enough. Does not
   * check if the instance is compatible with the dataset.
   * Note: string or relational values are not transferred.
   *
   * @param instance the instance to be added
   */
  void add(/*@non_NULL@*/ Instance instance) {

    Instance newInstance = (Instance)instance.copy();

    newInstance.setDataset(this);
    m_Instances.addElement(newInstance);
  }

  /**
   * Returns an attribute.
   *
   * @param index the attribute's index (index starts with 0)
   * @return the attribute at the given position
   */
  //@ requires 0 <= index;
  //@ requires index < m_Attributes.size();
  //@ ensures \result != NULL;
  /*@pure@*/ Attribute attribute(int index) {

    return (Attribute) m_Attributes.elementAt(index);
  }

  /**
   * Returns an attribute given its name. If there is more than
   * one attribute with the same name, it returns the first one.
   * Returns NULL if the attribute can't be found.
   *
   * @param name the attribute's name
   * @return the attribute with the given name, NULL if the
   * attribute can't be found
   */
  /*@pure@*/ Attribute attribute(string name) {

    for (int i = 0; i < numAttributes(); i++) {
      if (attribute(i).name().equals(name)) {
	return attribute(i);
      }
    }
    return NULL;
  }

  /**
   * Checks for attributes of the given type in the dataset
   *
   * @param attType  the attribute type to look for
   * @return         true if attributes of the given type are present
   */
  bool checkForAttributeType(int attType) {

    int i = 0;

    while (i < m_Attributes.size()) {
      if (attribute(i++).type() == attType) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks for string attributes in the dataset
   *
   * @return true if string attributes are present, false otherwise
   */
  /*@pure@*/ bool checkForStringAttributes() {
    return checkForAttributeType(Attribute.STRING);
  }

  /**
   * Checks if the given instance is compatible
   * with this dataset. Only looks at the size of
   * the instance and the ranges of the values for
   * nominal and string attributes.
   *
   * @param instance the instance to check
   * @return true if the instance is compatible with the dataset
   */
  /*@pure@*/ bool checkInstance(Instance instance);

  /**
   * Returns the class attribute.
   *
   * @return the class attribute
   * @throws UnassignedClassException if the class is not set
   */
  //@ requires classIndex() >= 0;
  /*@pure@*/ Attribute classAttribute() {

    if (m_ClassIndex < 0) {
      throw new UnassignedClassException("Class index is negative (not set)!");
    }
    return attribute(m_ClassIndex);
  }

  /**
   * Returns the class attribute's index. Returns negative number
   * if it's undefined.
   *
   * @return the class index as an integer
   */
  // ensures \result == m_ClassIndex;
  /*@pure@*/ int classIndex() {

    return m_ClassIndex;
  }

  /**
   * Compactifies the set of instances. Decreases the capacity of
   * the set so that it matches the number of instances in the set.
   */
  void compactify() {

    m_Instances.trimToSize();
  }

  /**
   * Removes all instances from the set.
   */
  void delete() {

    m_Instances = new FastVector();
  }

  /**
   * Removes an instance at the given position from the set.
   *
   * @param index the instance's position (index starts with 0)
   */
  //@ requires 0 <= index && index < numInstances();
  void delete(int index) {

    m_Instances.removeElementAt(index);
  }

  /**
   * Deletes an attribute at the given position
   * (0 to numAttributes() - 1). A deep copy of the attribute
   * information is performed before the attribute is deleted.
   *
   * @param position the attribute's position (position starts with 0)
   * @throws IllegalArgumentException if the given index is out of range
   *            or the class attribute is being deleted
   */
  //@ requires 0 <= position && position < numAttributes();
  //@ requires position != classIndex();
  void deleteAttributeAt(int position);

  /**
   * Deletes all attributes of the given type in the dataset. A deep copy of
   * the attribute information is performed before an attribute is deleted.
   *
   * @param attType the attribute type to delete
   * @throws IllegalArgumentException if attribute couldn't be
   * successfully deleted (probably because it is the class attribute).
   */
  void deleteAttributeType(int attType);

  /**
   * Deletes all string attributes in the dataset. A deep copy of the attribute
   * information is performed before an attribute is deleted.
   *
   * @throws IllegalArgumentException if string attribute couldn't be
   * successfully deleted (probably because it is the class attribute).
   * @see #deleteAttributeType(int)
   */
  void deleteStringAttributes() {
    deleteAttributeType(Attribute.STRING);
  }

  /**
   * Removes all instances with missing values for a particular
   * attribute from the dataset.
   *
   * @param attIndex the attribute's index (index starts with 0)
   */
  //@ requires 0 <= attIndex && attIndex < numAttributes();
  void deleteWithMissing(int attIndex);

  /**
   * Removes all instances with missing values for a particular
   * attribute from the dataset.
   *
   * @param att the attribute
   */
  void deleteWithMissing(/*@non_NULL@*/ Attribute att) {

    deleteWithMissing(att.index());
  }

  /**
   * Removes all instances with a missing class value
   * from the dataset.
   *
   * @throws UnassignedClassException if class is not set
   */
  void deleteWithMissingClass() {

    if (m_ClassIndex < 0) {
      throw new UnassignedClassException("Class index is negative (not set)!");
    }
    deleteWithMissing(m_ClassIndex);
  }

  /**
   * Returns an enumeration of all the attributes.
   *
   * @return enumeration of all the attributes.
   */
  /*@non_NULL pure@*/ Enumeration enumerateAttributes() {

    return m_Attributes.elements(m_ClassIndex);
  }

  /**
   * Returns an enumeration of all instances in the dataset.
   *
   * @return enumeration of all instances in the dataset
   */
  /*@non_NULL pure@*/ Enumeration enumerateInstances() {

    return m_Instances.elements();
  }

  /**
   * Checks if two headers are equivalent.
   *
   * @param dataset another dataset
   * @return true if the header of the given dataset is equivalent
   * to this header
   */
  /*@pure@*/ bool equalHeaders(Instances dataset);

  /**
   * Returns the first instance in the set.
   *
   * @return the first instance in the set
   */
  //@ requires numInstances() > 0;
  /*@non_NULL pure@*/ Instance firstInstance() {

    return (Instance)m_Instances.firstElement();
  }

  /**
   * Returns a random number generator. The initial seed of the random
   * number generator depends on the given seed and the hash code of
   * a string representation of a instances chosen based on the given
   * seed.
   *
   * @param seed the given seed
   * @return the random number generator
   */
  Random getRandomNumberGenerator(long seed) {

    Random r = new Random(seed);
    r.setSeed(instance(r.nextInt(numInstances())).toStringNoWeight().hashCode() + seed);
    return r;
  }

  /**
   * Inserts an attribute at the given position (0 to
   * numAttributes()) and sets all values to be missing.
   * Shallow copies the attribute before it is inserted, and performs
   * a deep copy of the existing attribute information.
   *
   * @param att the attribute to be inserted
   * @param position the attribute's position (position starts with 0)
   * @throws IllegalArgumentException if the given index is out of range
   */
  //@ requires 0 <= position;
  //@ requires position <= numAttributes();
  void insertAttributeAt(/*@non_NULL@*/ Attribute att, int position);

  /**
   * Returns the instance at the given position.
   *
   * @param index the instance's index (index starts with 0)
   * @return the instance at the given position
   */
  //@ requires 0 <= index;
  //@ requires index < numInstances();
  /*@non_NULL pure@*/ Instance instance(int index) {

    return (Instance)m_Instances.elementAt(index);
  }

  /**
   * Returns the kth-smallest attribute value of a numeric attribute.
   * Note that calling this method will change the order of the data!
   *
   * @param att the Attribute object
   * @param k the value of k
   * @return the kth-smallest value
   */
  double kthSmallestValue(Attribute att, int k) {

    return kthSmallestValue(att.index(), k);
  }

  /**
   * Returns the kth-smallest attribute value of a numeric attribute.
   * Note that calling this method will change the order of the data!
   * The number of non-missing values in the data must be as least
   * as last as k for this to work.
   *
   * @param attIndex the attribute's index
   * @param k the value of k
   * @return the kth-smallest value
   */
  double kthSmallestValue(int attIndex, int k);

  /**
   * Returns the last instance in the set.
   *
   * @return the last instance in the set
   */
  //@ requires numInstances() > 0;
  /*@non_NULL pure@*/ Instance lastInstance() {

    return (Instance)m_Instances.lastElement();
  }

  /**
   * Returns the mean (mode) for a numeric (nominal) attribute as
   * a floating-point value. Returns 0 if the attribute is neither nominal nor
   * numeric. If all values are missing it returns zero.
   *
   * @param attIndex the attribute's index (index starts with 0)
   * @return the mean or the mode
   */
  /*@pure@*/ double meanOrMode(int attIndex);

  /**
   * Returns the mean (mode) for a numeric (nominal) attribute as a
   * floating-point value.  Returns 0 if the attribute is neither
   * nominal nor numeric.  If all values are missing it returns zero.
   *
   * @param att the attribute
   * @return the mean or the mode
   */
  /*@pure@*/ double meanOrMode(Attribute att) {

    return meanOrMode(att.index());
  }

  /**
   * Returns the number of attributes.
   *
   * @return the number of attributes as an integer
   */
  //@ ensures \result == m_Attributes.size();
  /*@pure@*/ int numAttributes() {

    return m_Attributes.size();
  }

  /**
   * Returns the number of class labels.
   *
   * @return the number of class labels as an integer if the class
   * attribute is nominal, 1 otherwise.
   * @throws UnassignedClassException if the class is not set
   */
  //@ requires classIndex() >= 0;
  /*@pure@*/ int numClasses() {

    if (m_ClassIndex < 0) {
      throw new UnassignedClassException("Class index is negative (not set)!");
    }
    if (!classAttribute().isNominal()) {
      return 1;
    } else {
      return classAttribute().numValues();
    }
  }

  /**
   * Returns the number of distinct values of a given attribute.
   * Returns the number of instances if the attribute is a
   * string attribute. The value 'missing' is not counted.
   *
   * @param attIndex the attribute (index starts with 0)
   * @return the number of distinct values of a given attribute
   */
  //@ requires 0 <= attIndex;
  //@ requires attIndex < numAttributes();
  /*@pure@*/ int numDistinctValues(int attIndex);

  /**
   * Returns the number of distinct values of a given attribute.
   * Returns the number of instances if the attribute is a
   * string attribute. The value 'missing' is not counted.
   *
   * @param att the attribute
   * @return the number of distinct values of a given attribute
   */
  /*@pure@*/ int numDistinctValues(/*@non_NULL@*/Attribute att) {

    return numDistinctValues(att.index());
  }

  /**
   * Returns the number of instances in the dataset.
   *
   * @return the number of instances in the dataset as an integer
   */
  //@ ensures \result == m_Instances.size();
  /*@pure@*/ int numInstances() {

    return m_Instances.size();
  }

  /**
   * Shuffles the instances in the set so that they are ordered
   * randomly.
   *
   * @param random a random number generator
   */
  void randomize(Random random);

  /**
   * Reads a single instance from the reader and appends it
   * to the dataset.  Automatically expands the dataset if it
   * is not large enough to hold the instance. This method does
   * not check for carriage return at the end of the line.
   *
   * @param reader the reader
   * @return false if end of file has been reached
   * @throws IOException if the information is not read
   * successfully
   * @deprecated instead of using this method in conjunction with the
   * <code>readInstance(Reader)</code> method, one should use the
   * <code>ArffLoader</code> or <code>DataSource</code> class instead.
   * @see weka.core.converters.ArffLoader
   * @see weka.core.converters.ConverterUtils.DataSource
   */
  bool readInstance(Reader reader) throw(IOException) {

    ArffReader arff = new ArffReader(reader, this, m_Lines, 1);
    Instance inst = arff.readInstance(arff.getData(), false);
    m_Lines = arff.getLineNo();
    if (inst != NULL) {
      add(inst);
      return true;
    }
    else {
      return false;
    }
  }

  /**
   * Returns the relation's name.
   *
   * @return the relation's name as a string
   */
  //@ ensures \result == m_RelationName;
  /*@pure@*/ string relationName() {

    return m_RelationName;
  }

  /**
   * Renames an attribute. This change only affects this
   * dataset.
   *
   * @param att the attribute's index (index starts with 0)
   * @param name the new name
   */
  void renameAttribute(int att, string name);

  /**
   * Renames an attribute. This change only affects this
   * dataset.
   *
   * @param att the attribute
   * @param name the new name
   */
  void renameAttribute(Attribute att, string name) {

    renameAttribute(att.index(), name);
  }

  /**
   * Renames the value of a nominal (or string) attribute value. This
   * change only affects this dataset.
   *
   * @param att the attribute's index (index starts with 0)
   * @param val the value's index (index starts with 0)
   * @param name the new name
   */
  void renameAttributeValue(int att, int val, string name);

  /**
   * Renames the value of a nominal (or string) attribute value. This
   * change only affects this dataset.
   *
   * @param att the attribute
   * @param val the value
   * @param name the new name
   */
  void renameAttributeValue(Attribute att, string val,
                                         string name) {

    int v = att.indexOfValue(val);
    if (v == -1) throw new IllegalArgumentException(val + " not found");
    renameAttributeValue(att.index(), v, name);
  }

  /**
   * Creates a new dataset of the same size using random sampling
   * with replacement.
   *
   * @param random a random number generator
   * @return the new dataset
   */
  Instances resample(Random random);

  /**
   * Creates a new dataset of the same size using random sampling
   * with replacement according to the current instance weights. The
   * weights of the instances in the new dataset are set to one.
   *
   * @param random a random number generator
   * @return the new dataset
   */
  Instances resampleWithWeights(Random random);

  /**
   * Creates a new dataset of the same size using random sampling
   * with replacement according to the given weight vector. The
   * weights of the instances in the new dataset are set to one.
   * The length of the weight vector has to be the same as the
   * number of instances in the dataset, and all weights have to
   * be positive.
   *
   * @param random a random number generator
   * @param weights the weight vector
   * @return the new dataset
   * @throws IllegalArgumentException if the weights array is of the wrong
   * length or contains negative weights.
   */
  Instances resampleWithWeights(Random random, double[] weights);

  /**
   * Sets the class attribute.
   *
   * @param att attribute to be the class
   */
  void setClass(Attribute att) {

    m_ClassIndex = att.index();
  }

  /**
   * Sets the class index of the set.
   * If the class index is negative there is assumed to be no class.
   * (ie. it is undefined)
   *
   * @param classIndex the new class index (index starts with 0)
   * @throws IllegalArgumentException if the class index is too big or < 0
   */
  void setClassIndex(int classIndex) {

    if (classIndex >= numAttributes()) {
      throw new IllegalArgumentException("Invalid class index: " + classIndex);
    }
    m_ClassIndex = classIndex;
  }

  /**
   * Sets the relation's name.
   *
   * @param newName the new relation name.
   */
  void setRelationName(/*@non_NULL@*/string newName) {

    m_RelationName = newName;
  }

  /**
   * Sorts the instances based on an attribute. For numeric attributes,
   * instances are sorted in ascending order. For nominal attributes,
   * instances are sorted based on the attribute label ordering
   * specified in the header. Instances with missing values for the
   * attribute are placed at the end of the dataset.
   *
   * @param attIndex the attribute's index (index starts with 0)
   */
  void sort(int attIndex);

  /**
   * Sorts the instances based on an attribute. For numeric attributes,
   * instances are sorted into ascending order. For nominal attributes,
   * instances are sorted based on the attribute label ordering
   * specified in the header. Instances with missing values for the
   * attribute are placed at the end of the dataset.
   *
   * @param att the attribute
   */
  void sort(Attribute att) {

    sort(att.index());
  }

  /**
   * Stratifies a set of instances according to its class values
   * if the class attribute is nominal (so that afterwards a
   * stratified cross-validation can be performed).
   *
   * @param numFolds the number of folds in the cross-validation
   * @throws UnassignedClassException if the class is not set
   */
  void stratify(int numFolds);

  /**
   * Computes the sum of all the instances' weights.
   *
   * @return the sum of all the instances' weights as a double
   */
  /*@pure@*/ double sumOfWeights() {

    double sum = 0;

    for (int i = 0; i < numInstances(); i++) {
      sum += instance(i).weight();
    }
    return sum;
  }

  /**
   * Creates the test set for one fold of a cross-validation on
   * the dataset.
   *
   * @param numFolds the number of folds in the cross-validation. Must
   * be greater than 1.
   * @param numFold 0 for the first fold, 1 for the second, ...
   * @return the test set as a set of weighted instances
   * @throws IllegalArgumentException if the number of folds is less than 2
   * or greater than the number of instances.
   */
  //@ requires 2 <= numFolds && numFolds < numInstances();
  //@ requires 0 <= numFold && numFold < numFolds;
  Instances testCV(int numFolds, int numFold);

  /**
   * Returns the dataset as a string in ARFF format. Strings
   * are quoted if they contain whitespace characters, or if they
   * are a question mark.
   *
   * @return the dataset in ARFF format as a string
   */
  string toString();

  /**
   * Returns the instances in the dataset as a string in ARFF format. Strings
   * are quoted if they contain whitespace characters, or if they
   * are a question mark.
   *
   * @return the dataset in ARFF format as a string
   */
protected:
  string stringWithoutHeader();

public:
  /**
   * Creates the training set for one fold of a cross-validation
   * on the dataset.
   *
   * @param numFolds the number of folds in the cross-validation. Must
   * be greater than 1.
   * @param numFold 0 for the first fold, 1 for the second, ...
   * @return the training set
   * @throws IllegalArgumentException if the number of folds is less than 2
   * or greater than the number of instances.
   */
  //@ requires 2 <= numFolds && numFolds < numInstances();
  //@ requires 0 <= numFold && numFold < numFolds;
  Instances trainCV(int numFolds, int numFold);

  /**
   * Creates the training set for one fold of a cross-validation
   * on the dataset. The data is subsequently randomized based
   * on the given random number generator.
   *
   * @param numFolds the number of folds in the cross-validation. Must
   * be greater than 1.
   * @param numFold 0 for the first fold, 1 for the second, ...
   * @param random the random number generator
   * @return the training set
   * @throws IllegalArgumentException if the number of folds is less than 2
   * or greater than the number of instances.
   */
  //@ requires 2 <= numFolds && numFolds < numInstances();
  //@ requires 0 <= numFold && numFold < numFolds;
  Instances trainCV(int numFolds, int numFold, Random random);

  /**
   * Computes the variance for a numeric attribute.
   *
   * @param attIndex the numeric attribute (index starts with 0)
   * @return the variance if the attribute is numeric
   * @throws IllegalArgumentException if the attribute is not numeric
   */
  /*@pure@*/ double variance(int attIndex);

  /**
   * Computes the variance for a numeric attribute.
   *
   * @param att the numeric attribute
   * @return the variance if the attribute is numeric
   * @throws IllegalArgumentException if the attribute is not numeric
   */
  /*@pure@*/ double variance(Attribute att) {

    return variance(att.index());
  }

  /**
   * Calculates summary statistics on the values that appear in this
   * set of instances for a specified attribute.
   *
   * @param index the index of the attribute to summarize (index starts with 0)
   * @return an AttributeStats object with it's fields calculated.
   */
  //@ requires 0 <= index && index < numAttributes();
  AttributeStats attributeStats(int index);

  /**
   * Gets the value of all instances in this dataset for a particular
   * attribute. Useful in conjunction with Utils.sort to allow iterating
   * through the dataset in sorted order for some attribute.
   *
   * @param index the index of the attribute.
   * @return an array containing the value of the desired attribute for
   * each instance in the dataset.
   */
  //@ requires 0 <= index && index < numAttributes();
  /*@pure@*/ double [] attributeToDoubleArray(int index);

  /**
   * Generates a string summarizing the set of instances. Gives a breakdown
   * for each attribute indicating the number of missing/discrete/unique
   * values and other information.
   *
   * @return a string summarizing the dataset
   */
  string toSummaryString();

protected:
  /**
   * Copies instances from one set to the end of another
   * one.
   *
   * @param from the position of the first instance to be copied
   * @param dest the destination for the instances
   * @param num the number of instances to be copied
   */
  //@ requires 0 <= from && from <= numInstances() - num;
  //@ requires 0 <= num;
  void copyInstances(int from, /*@non_NULL@*/ Instances dest, int num);

  /**
   * Replaces the attribute information by a clone of
   * itself.
   */
  void freshAttributeInfo() {

    m_Attributes = (FastVector) m_Attributes.copyElements();
  }

  /**
   * Returns string including all instances, their weights and
   * their indices in the original dataset.
   *
   * @return description of instance and its weight as a string
   */
  /*@pure@*/ string instancesAndWeights();

  /**
   * Partitions the instances around a pivot. Used by quicksort and
   * kthSmallestValue.
   *
   * @param attIndex the attribute's index (index starts with 0)
   * @param l the first index of the subset (index starts with 0)
   * @param r the last index of the subset (index starts with 0)
   *
   * @return the index of the middle element
   */
  //@ requires 0 <= attIndex && attIndex < numAttributes();
  //@ requires 0 <= left && left <= right && right < numInstances();
  int partition(int attIndex, int l, int r);

  /**
   * Implements quicksort according to Manber's "Introduction to
   * Algorithms".
   *
   * @param attIndex the attribute's index (index starts with 0)
   * @param left the first index of the subset to be sorted (index starts with 0)
   * @param right the last index of the subset to be sorted (index starts with 0)
   */
  //@ requires 0 <= attIndex && attIndex < numAttributes();
  //@ requires 0 <= first && first <= right && right < numInstances();
  void quickSort(int attIndex, int left, int right);

  /**
   * Implements computation of the kth-smallest element according
   * to Manber's "Introduction to Algorithms".
   *
   * @param attIndex the attribute's index (index starts with 0)
   * @param left the first index of the subset (index starts with 0)
   * @param right the last index of the subset (index starts with 0)
   * @param k the value of k
   *
   * @return the index of the kth-smallest element
   */
  //@ requires 0 <= attIndex && attIndex < numAttributes();
  //@ requires 0 <= first && first <= right && right < numInstances();
  int select(int attIndex, int left, int right, int k);

  /**
   * Help function needed for stratification of set.
   *
   * @param numFolds the number of folds for the stratification
   */
  void stratStep (int numFolds);

public:
  /**
   * Swaps two instances in the set.
   *
   * @param i the first instance's index (index starts with 0)
   * @param j the second instance's index (index starts with 0)
   */
  //@ requires 0 <= i && i < numInstances();
  //@ requires 0 <= j && j < numInstances();
  void swap(int i, int j){

    m_Instances.swap(i, j);
  }

  /**
   * Merges two sets of Instances together. The resulting set will have
   * all the attributes of the first set plus all the attributes of the
   * second set. The number of instances in both sets must be the same.
   *
   * @param first the first set of Instances
   * @param second the second set of Instances
   * @return the merged set of Instances
   * @throws IllegalArgumentException if the datasets are not the same size
   */
  static Instances mergeInstances(Instances first, Instances second);

  /**
   * Method for testing this class.
   *
   * @param argv should contain one element: the name of an ARFF file
   */
  //@ requires argv != NULL;
  //@ requires argv.length == 1;
  //@ requires argv[0] != NULL;
  static void test(string [] argv);

  /**
   * Returns the revision string.
   *
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 6996 $");
  }
};
