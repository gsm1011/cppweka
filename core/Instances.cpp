#include "Instances.hpp"

using namespace std; 

Instances::Instances(string name,
		   FastVector attInfo, int capacity) {

    // check whether the attribute names are unique
    HashSet<String> names = new HashSet<String>();
    StringBuffer nonUniqueNames = new StringBuffer();
    for (int i = 0; i < attInfo.size(); i++) {
      if (names.contains(((Attribute) attInfo.elementAt(i)).name())) {
        nonUniqueNames.append("'" + ((Attribute) attInfo.elementAt(i)).name() +"' ");
      }
      names.add(((Attribute) attInfo.elementAt(i)).name());
    }
    if (names.size() != attInfo.size())
      throw IllegalArgumentException("Attribute names are not unique!" +
          " Causes: " + nonUniqueNames.toString());
    names.clear();

    m_RelationName = name;
    m_ClassIndex = -1;
    m_Attributes = attInfo;
    for (int i = 0; i < numAttributes(); i++) {
      attribute(i).setIndex(i);
    }
    m_Instances = new FastVector(capacity);
  }


Instances Instances::stringFreeStructure() {

    FastVector newAtts = new FastVector();
    for (int i = 0 ; i < m_Attributes.size(); i++) {
      Attribute att = (Attribute)m_Attributes.elementAt(i);
      if (att.type() == Attribute.STRING) {
        newAtts.addElement(new Attribute(att.name(), (FastVector)NULL, i));
      } else if (att.type() == Attribute.RELATIONAL) {
        newAtts.addElement(new Attribute(att.name(), new Instances(att.relation(), 0), i));
      }
    }
    if (newAtts.size() == 0) {
      return new Instances(this, 0);
    }
    FastVector atts = (FastVector)m_Attributes.copy();
    for (int i = 0; i < newAtts.size(); i++) {
      atts.setElementAt(newAtts.elementAt(i), ((Attribute)newAtts.elementAt(i)).index());
    }
    Instances result = new Instances(this, 0);
    result.m_Attributes = atts;
    return result;
  }

bool Instances::checkInstance(Instance instance) {

    if (instance.numAttributes() != numAttributes()) {
      return false;
    }
    for (int i = 0; i < numAttributes(); i++) {
      if (instance.isMissing(i)) {
	continue;
      } else if (attribute(i).isNominal() ||
		 attribute(i).isString()) {
	if (!(Utils.eq(instance.value(i),
		       (double)(int)instance.value(i)))) {
	  return false;
	} else if (Utils.sm(instance.value(i), 0) ||
		   Utils.gr(instance.value(i),
			    attribute(i).numValues())) {
	  return false;
	}
      }
    }
    return true;
  }


void Instances::deleteAttributeAt(int position) {

    if ((position < 0) || (position >= m_Attributes.size())) {
      throw IllegalArgumentException("Index out of range");
    }
    if (position == m_ClassIndex) {
      throw IllegalArgumentException("Can't delete class attribute");
    }
    freshAttributeInfo();
    if (m_ClassIndex > position) {
      m_ClassIndex--;
    }
    m_Attributes.removeElementAt(position);
    for (int i = position; i < m_Attributes.size(); i++) {
      Attribute current = (Attribute)m_Attributes.elementAt(i);
      current.setIndex(current.index() - 1);
    }
    for (int i = 0; i < numInstances(); i++) {
      instance(i).forceDeleteAttributeAt(position);
    }
  }

void Instances::deleteAttributeType(int attType) {
    int i = 0;
    while (i < m_Attributes.size()) {
      if (attribute(i).type() == attType) {
        deleteAttributeAt(i);
      } else {
        i++;
      }
    }
  }

  /**
   * Removes all instances with missing values for a particular
   * attribute from the dataset.
   *
   * @param attIndex the attribute's index (index starts with 0)
   */
  //@ requires 0 <= attIndex && attIndex < numAttributes();
void Instances::deleteWithMissing(int attIndex) {

    FastVector newInstances = new FastVector(numInstances());

    for (int i = 0; i < numInstances(); i++) {
      if (!instance(i).isMissing(attIndex)) {
	newInstances.addElement(instance(i));
      }
    }
    m_Instances = newInstances;
  }

  /**
   * Checks if two headers are equivalent.
   *
   * @param dataset another dataset
   * @return true if the header of the given dataset is equivalent
   * to this header
   */
/ bool Instances::equalHeaders(Instances dataset){

    // Check class and all attributes
    if (m_ClassIndex != dataset.m_ClassIndex) {
      return false;
    }
    if (m_Attributes.size() != dataset.m_Attributes.size()) {
      return false;
    }
    for (int i = 0; i < m_Attributes.size(); i++) {
      if (!(attribute(i).equals(dataset.attribute(i)))) {
	return false;
      }
    }
    return true;
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
void Instances::insertAttributeAt(/*@non_NULL@*/ Attribute att, int position) {

    if ((position < 0) ||
	(position > m_Attributes.size())) {
      throw IllegalArgumentException("Index out of range");
    }
    if (attribute(att.name()) != NULL) {
      throw IllegalArgumentException(
	  "Attribute name '" + att.name() + "' already in use at position #" + attribute(att.name()).index());
    }
    att = (Attribute)att.copy();
    freshAttributeInfo();
    att.setIndex(position);
    m_Attributes.insertElementAt(att, position);
    for (int i = position + 1; i < m_Attributes.size(); i++) {
      Attribute current = (Attribute)m_Attributes.elementAt(i);
      current.setIndex(current.index() + 1);
    }
    for (int i = 0; i < numInstances(); i++) {
      instance(i).forceInsertAttributeAt(position);
    }
    if (m_ClassIndex >= position) {
      m_ClassIndex++;
    }
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
double Instances::kthSmallestValue(int attIndex, int k) {

    if (!attribute(attIndex).isNumeric()) {
      throw IllegalArgumentException("Instances: attribute must be numeric to compute kth-smallest value.");
    }

    int i,j;

    // move all instances with missing values to end
    j = numInstances() - 1;
    i = 0;
    while (i <= j) {
      if (instance(j).isMissing(attIndex)) {
	j--;
      } else {
	if (instance(i).isMissing(attIndex)) {
	  swap(i,j);
	  j--;
	}
	i++;
      }
    }

    if ((k < 1) || (k > j+1)) {
      throw IllegalArgumentException("Instances: value for k for computing kth-smallest value too large.");
    }

    return instance(select(attIndex, 0, j, k)).value(attIndex);
  }

  /**
   * Returns the mean (mode) for a numeric (nominal) attribute as
   * a floating-point value. Returns 0 if the attribute is neither nominal nor
   * numeric. If all values are missing it returns zero.
   *
   * @param attIndex the attribute's index (index starts with 0)
   * @return the mean or the mode
   */
double Instances::meanOrMode(int attIndex) {

    double result, found;
    int [] counts;

    if (attribute(attIndex).isNumeric()) {
      result = found = 0;
      for (int j = 0; j < numInstances(); j++) {
	if (!instance(j).isMissing(attIndex)) {
	  found += instance(j).weight();
	  result += instance(j).weight()*instance(j).value(attIndex);
	}
      }
      if (found <= 0) {
	return 0;
      } else {
	return result / found;
      }
    } else if (attribute(attIndex).isNominal()) {
      counts = new int[attribute(attIndex).numValues()];
      for (int j = 0; j < numInstances(); j++) {
	if (!instance(j).isMissing(attIndex)) {
	  counts[(int) instance(j).value(attIndex)] += instance(j).weight();
	}
      }
      return (double)Utils.maxIndex(counts);
    } else {
      return 0;
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
int Instances::numDistinctValues(int attIndex) {

    if (attribute(attIndex).isNumeric()) {
      double [] attVals = attributeToDoubleArray(attIndex);
      int [] sorted = Utils.sort(attVals);
      double prev = 0;
      int counter = 0;
      for (int i = 0; i < sorted.length; i++) {
	Instance current = instance(sorted[i]);
	if (current.isMissing(attIndex)) {
	  break;
	}
	if ((i == 0) ||
	    (current.value(attIndex) > prev)) {
	  prev = current.value(attIndex);
	  counter++;
	}
      }
      return counter;
    } else {
      return attribute(attIndex).numValues();
    }
  }



  /**
   * Shuffles the instances in the set so that they are ordered
   * randomly.
   *
   * @param random a random number generator
   */
void Instances::randomize(Random random) {

    for (int j = numInstances() - 1; j > 0; j--)
      swap(j, random.nextInt(j+1));
  }

  /**
   * Renames an attribute. This change only affects this
   * dataset.
   *
   * @param att the attribute's index (index starts with 0)
   * @param name the new name
   */
void Instances::renameAttribute(int att, string name) {
    // name already present?
    for (int i = 0; i < numAttributes(); i++) {
      if (i == att)
	continue;
      if (attribute(i).name().equals(name)) {
	throw IllegalArgumentException(
	    "Attribute name '" + name + "' already present at position #" + i);
      }
    }

    Attribute newAtt = attribute(att).copy(name);
    FastVector newVec = new FastVector(numAttributes());
    for (int i = 0; i < numAttributes(); i++) {
      if (i == att) {
	newVec.addElement(newAtt);
      } else {
	newVec.addElement(attribute(i));
      }
    }
    m_Attributes = newVec;
  }


  /**
   * Renames the value of a nominal (or string) attribute value. This
   * change only affects this dataset.
   *
   * @param att the attribute's index (index starts with 0)
   * @param val the value's index (index starts with 0)
   * @param name the new name
   */
void Instances::renameAttributeValue(int att, int val, string name) {

    Attribute newAtt = (Attribute)attribute(att).copy();
    FastVector newVec = new FastVector(numAttributes());

    newAtt.setValue(val, name);
    for (int i = 0; i < numAttributes(); i++) {
      if (i == att) {
	newVec.addElement(newAtt);
      } else {
	newVec.addElement(attribute(i));
      }
    }
    m_Attributes = newVec;
  }

  /**
   * Creates a new dataset of the same size using random sampling
   * with replacement.
   *
   * @param random a random number generator
   * @return the new dataset
   */
Instances Instances::resample(Random random) {

    Instances newData = new Instances(this, numInstances());
    while (newData.numInstances() < numInstances()) {
      newData.add(instance(random.nextInt(numInstances())));
    }
    return newData;
  }

  /**
   * Creates a new dataset of the same size using random sampling
   * with replacement according to the current instance weights. The
   * weights of the instances in the new dataset are set to one.
   *
   * @param random a random number generator
   * @return the new dataset
   */
Instances Instances::resampleWithWeights(Random random) {

    double [] weights = new double[numInstances()];
    for (int i = 0; i < weights.length; i++) {
      weights[i] = instance(i).weight();
    }
    return resampleWithWeights(random, weights);
  }


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
Instances Instances::resampleWithWeights(Random random,
					     double[] weights) {

    if (weights.length != numInstances()) {
      throw IllegalArgumentException("weights.length != numInstances.");
    }
    Instances newData = new Instances(this, numInstances());
    if (numInstances() == 0) {
      return newData;
    }
    double[] probabilities = new double[numInstances()];
    double sumProbs = 0, sumOfWeights = Utils.sum(weights);
    for (int i = 0; i < numInstances(); i++) {
      sumProbs += random.nextDouble();
      probabilities[i] = sumProbs;
    }
    Utils.normalize(probabilities, sumProbs / sumOfWeights);

    // Make sure that rounding errors don't mess things up
    probabilities[numInstances() - 1] = sumOfWeights;
    int k = 0; int l = 0;
    sumProbs = 0;
    while ((k < numInstances() && (l < numInstances()))) {
      if (weights[l] < 0) {
	throw IllegalArgumentException("Weights have to be positive.");
      }
      sumProbs += weights[l];
      while ((k < numInstances()) &&
	     (probabilities[k] <= sumProbs)) {
	newData.add(instance(l));
	newData.instance(k).setWeight(1);
	k++;
      }
      l++;
    }
    return newData;
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
void Instances::sort(int attIndex) {

    int i,j;

    // move all instances with missing values to end
    j = numInstances() - 1;
    i = 0;
    while (i <= j) {
      if (instance(j).isMissing(attIndex)) {
	j--;
      } else {
	if (instance(i).isMissing(attIndex)) {
	  swap(i,j);
	  j--;
	}
	i++;
      }
    }
    quickSort(attIndex, 0, j);
  }

  /**
   * Stratifies a set of instances according to its class values
   * if the class attribute is nominal (so that afterwards a
   * stratified cross-validation can be performed).
   *
   * @param numFolds the number of folds in the cross-validation
   * @throws UnassignedClassException if the class is not set
   */
void Instances::stratify(int numFolds) {

    if (numFolds <= 1) {
      throw IllegalArgumentException("Number of folds must be greater than 1");
    }
    if (m_ClassIndex < 0) {
      throw UnassignedClassException("Class index is negative (not set)!");
    }
    if (classAttribute().isNominal()) {

      // sort by class
      int index = 1;
      while (index < numInstances()) {
	Instance instance1 = instance(index - 1);
	for (int j = index; j < numInstances(); j++) {
	  Instance instance2 = instance(j);
	  if ((instance1.classValue() == instance2.classValue()) ||
	      (instance1.classIsMissing() &&
	       instance2.classIsMissing())) {
	    swap(index,j);
	    index++;
	  }
	}
	index++;
      }
      stratStep(numFolds);
    }
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
Instances Instances::testCV(int numFolds, int numFold) {

    int numInstForFold, first, offset;
    Instances test;

    if (numFolds < 2) {
      throw IllegalArgumentException("Number of folds must be at least 2!");
    }
    if (numFolds > numInstances()) {
      throw IllegalArgumentException("Can't have more folds than instances!");
    }
    numInstForFold = numInstances() / numFolds;
    if (numFold < numInstances() % numFolds){
      numInstForFold++;
      offset = numFold;
    }else
      offset = numInstances() % numFolds;
    test = new Instances(this, numInstForFold);
    first = numFold * (numInstances() / numFolds) + offset;
    copyInstances(first, test, numInstForFold);
    return test;
  }

  /**
   * Returns the dataset as a string in ARFF format. Strings
   * are quoted if they contain whitespace characters, or if they
   * are a question mark.
   *
   * @return the dataset in ARFF format as a string
   */
string Instances::toString() {

    StringBuffer text = new StringBuffer();

    text.append(ARFF_RELATION).append(" ").
      append(Utils.quote(m_RelationName)).append("\n\n");
    for (int i = 0; i < numAttributes(); i++) {
      text.append(attribute(i)).append("\n");
    }
    text.append("\n").append(ARFF_DATA).append("\n");

    text.append(stringWithoutHeader());
    return text.toString();
  }

string Instances::stringWithoutHeader() {

    StringBuffer text = new StringBuffer();

    for (int i = 0; i < numInstances(); i++) {
      text.append(instance(i));
      if (i < numInstances() - 1) {
	text.append('\n');
      }
    }
    return text.toString();
  }

Instances Instances::trainCV(int numFolds, int numFold) {

    int numInstForFold, first, offset;
    Instances train;

    if (numFolds < 2) {
      throw IllegalArgumentException("Number of folds must be at least 2!");
    }
    if (numFolds > numInstances()) {
      throw IllegalArgumentException("Can't have more folds than instances!");
    }
    numInstForFold = numInstances() / numFolds;
    if (numFold < numInstances() % numFolds) {
      numInstForFold++;
      offset = numFold;
    }else
      offset = numInstances() % numFolds;
    train = new Instances(this, numInstances() - numInstForFold);
    first = numFold * (numInstances() / numFolds) + offset;
    copyInstances(0, train, first);
    copyInstances(first + numInstForFold, train,
		  numInstances() - first - numInstForFold);

    return train;
  }

Instances Instances::trainCV(int numFolds, int numFold, Random random) {

    Instances train = trainCV(numFolds, numFold);
    train.randomize(random);
    return train;
  }

double Instances::variance(int attIndex) {

    double sum = 0, sumSquared = 0, sumOfWeights = 0;

    if (!attribute(attIndex).isNumeric()) {
      throw IllegalArgumentException("Can't compute variance because attribute is " +
			  "not numeric!");
    }
    for (int i = 0; i < numInstances(); i++) {
      if (!instance(i).isMissing(attIndex)) {
	sum += instance(i).weight() *
	  instance(i).value(attIndex);
	sumSquared += instance(i).weight() *
	  instance(i).value(attIndex) *
	  instance(i).value(attIndex);
	sumOfWeights += instance(i).weight();
      }
    }
    if (sumOfWeights <= 1) {
      return 0;
    }
    double result = (sumSquared - (sum * sum / sumOfWeights)) /
      (sumOfWeights - 1);

    // We don't like negative variance
    if (result < 0) {
      return 0;
    } else {
      return result;
    }
  }

AttributeStats Instances::attributeStats(int index) {

    AttributeStats result = new AttributeStats();
    if (attribute(index).isNominal()) {
      result.nominalCounts = new int [attribute(index).numValues()];
    }
    if (attribute(index).isNumeric()) {
      result.numericStats = new weka.experiment.Stats();
    }
    result.totalCount = numInstances();

    double [] attVals = attributeToDoubleArray(index);
    int [] sorted = Utils.sort(attVals);
    int currentCount = 0;
    double prev = Instance.missingValue();
    for (int j = 0; j < numInstances(); j++) {
      Instance current = instance(sorted[j]);
      if (current.isMissing(index)) {
	result.missingCount = numInstances() - j;
	break;
      }
      if (current.value(index) == prev) {
	currentCount++;
      } else {
	result.addDistinct(prev, currentCount);
	currentCount = 1;
	prev = current.value(index);
      }
    }
    result.addDistinct(prev, currentCount);
    result.distinctCount--; // So we don't count "missing" as a value
    return result;
  }

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
double [] Instances::attributeToDoubleArray(int index) {

    double [] result = new double[numInstances()];
    for (int i = 0; i < result.length; i++) {
      result[i] = instance(i).value(index);
    }
    return result;
  }

  /**
   * Generates a string summarizing the set of instances. Gives a breakdown
   * for each attribute indicating the number of missing/discrete/unique
   * values and other information.
   *
   * @return a string summarizing the dataset
   */
string Instances::toSummaryString() {

    StringBuffer result = new StringBuffer();
    result.append("Relation Name:  ").append(relationName()).append('\n');
    result.append("Num Instances:  ").append(numInstances()).append('\n');
    result.append("Num Attributes: ").append(numAttributes()).append('\n');
    result.append('\n');

    result.append(Utils.padLeft("", 5)).append(Utils.padRight("Name", 25));
    result.append(Utils.padLeft("Type", 5)).append(Utils.padLeft("Nom", 5));
    result.append(Utils.padLeft("Int", 5)).append(Utils.padLeft("Real", 5));
    result.append(Utils.padLeft("Missing", 12));
    result.append(Utils.padLeft("Unique", 12));
    result.append(Utils.padLeft("Dist", 6)).append('\n');
    for (int i = 0; i < numAttributes(); i++) {
      Attribute a = attribute(i);
      AttributeStats as = attributeStats(i);
      result.append(Utils.padLeft("" + (i + 1), 4)).append(' ');
      result.append(Utils.padRight(a.name(), 25)).append(' ');
      long percent;
      switch (a.type()) {
      case Attribute.NOMINAL:
	result.append(Utils.padLeft("Nom", 4)).append(' ');
	percent = round(100.0 * as.intCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	result.append(Utils.padLeft("" + 0, 3)).append("% ");
	percent = round(100.0 * as.realCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	break;
      case Attribute.NUMERIC:
	result.append(Utils.padLeft("Num", 4)).append(' ');
	result.append(Utils.padLeft("" + 0, 3)).append("% ");
	percent = round(100.0 * as.intCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	percent = round(100.0 * as.realCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	break;
      case Attribute.DATE:
	result.append(Utils.padLeft("Dat", 4)).append(' ');
	result.append(Utils.padLeft("" + 0, 3)).append("% ");
	percent = round(100.0 * as.intCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	percent = round(100.0 * as.realCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	break;
      case Attribute.STRING:
	result.append(Utils.padLeft("Str", 4)).append(' ');
	percent = round(100.0 * as.intCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	result.append(Utils.padLeft("" + 0, 3)).append("% ");
	percent = round(100.0 * as.realCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	break;
      case Attribute.RELATIONAL:
	result.append(Utils.padLeft("Rel", 4)).append(' ');
	percent = round(100.0 * as.intCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	result.append(Utils.padLeft("" + 0, 3)).append("% ");
	percent = round(100.0 * as.realCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	break;
      default:
	result.append(Utils.padLeft("???", 4)).append(' ');
	result.append(Utils.padLeft("" + 0, 3)).append("% ");
	percent = round(100.0 * as.intCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	percent = round(100.0 * as.realCount / as.totalCount);
	result.append(Utils.padLeft("" + percent, 3)).append("% ");
	break;
      }
      result.append(Utils.padLeft("" + as.missingCount, 5)).append(" /");
      percent = round(100.0 * as.missingCount / as.totalCount);
      result.append(Utils.padLeft("" + percent, 3)).append("% ");
      result.append(Utils.padLeft("" + as.uniqueCount, 5)).append(" /");
      percent = round(100.0 * as.uniqueCount / as.totalCount);
      result.append(Utils.padLeft("" + percent, 3)).append("% ");
      result.append(Utils.padLeft("" + as.distinctCount, 5)).append(' ');
      result.append('\n');
    }
    return result.toString();
  }

void Instances::copyInstances(int from, Instances dest, int num) {

    for (int i = 0; i < num; i++) {
      dest.add(instance(from + i));
    }
  }

string Instances::instancesAndWeights(){

    StringBuffer text = new StringBuffer();

    for (int i = 0; i < numInstances(); i++) {
      text.append(instance(i) + " " + instance(i).weight());
      if (i < numInstances() - 1) {
	text.append("\n");
      }
    }
    return text.toString();
  }

int Instances::partition(int attIndex, int l, int r) {

    double pivot = instance((l + r) / 2).value(attIndex);

    while (l < r) {
      while ((instance(l).value(attIndex) < pivot) && (l < r)) {
        l++;
      }
      while ((instance(r).value(attIndex) > pivot) && (l < r)) {
        r--;
      }
      if (l < r) {
        swap(l, r);
        l++;
        r--;
      }
    }
    if ((l == r) && (instance(r).value(attIndex) > pivot)) {
      r--;
    }

    return r;
  }

void Instances::quickSort(int attIndex, int left, int right) {

    if (left < right) {
      int middle = partition(attIndex, left, right);
      quickSort(attIndex, left, middle);
      quickSort(attIndex, middle + 1, right);
    }
  }

int Instances::select(int attIndex, int left, int right, int k) {

    if (left == right) {
      return left;
    } else {
      int middle = partition(attIndex, left, right);
      if ((middle - left + 1) >= k) {
        return select(attIndex, left, middle, k);
      } else {
        return select(attIndex, middle + 1, right, k - (middle - left + 1));
      }
    }
  }

void Instances::stratStep (int numFolds){

    FastVector newVec = new FastVector(m_Instances.capacity());
    int start = 0, j;

    // create stratified batch
    while (newVec.size() < numInstances()) {
      j = start;
      while (j < numInstances()) {
	newVec.addElement(instance(j));
	j = j + numFolds;
      }
      start++;
    }
    m_Instances = newVec;
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
static Instances Instances::mergeInstances(Instances first, Instances second) {

    if (first.numInstances() != second.numInstances()) {
      throw IllegalArgumentException("Instance sets must be of the same size");
    }

    // Create the vector of merged attributes
    FastVector newAttributes = new FastVector();
    for (int i = 0; i < first.numAttributes(); i++) {
      newAttributes.addElement(first.attribute(i));
    }
    for (int i = 0; i < second.numAttributes(); i++) {
      newAttributes.addElement(second.attribute(i));
    }

    // Create the set of Instances
    Instances merged = new Instances(first.relationName() + '_'
				     + second.relationName(),
				     newAttributes,
				     first.numInstances());
    // Merge each instance
    for (int i = 0; i < first.numInstances(); i++) {
      merged.add(first.instance(i).mergeInstance(second.instance(i)));
    }
    return merged;
  }

static void Instances::test(string [] argv) {

    Instances instances, secondInstances, train, test, empty;
    Random random = new Random(2);
    Reader reader;
    int start, num;
    FastVector testAtts, testVals;
    int i,j;

    try{
      if (argv.length > 1) {
	throw (new Exception("Usage: Instances [<filename>]"));
      }

      // Creating set of instances from scratch
      testVals = new FastVector(2);
      testVals.addElement("first_value");
      testVals.addElement("second_value");
      testAtts = new FastVector(2);
      testAtts.addElement(new Attribute("nominal_attribute", testVals));
      testAtts.addElement(new Attribute("numeric_attribute"));
      instances = new Instances("test_set", testAtts, 10);
      instances.add(new Instance(instances.numAttributes()));
      instances.add(new Instance(instances.numAttributes()));
      instances.add(new Instance(instances.numAttributes()));
      instances.setClassIndex(0);
      cout << "\nSet of instances created from scratch:\n" << endl; 
      cout << instances << endl; 

      if (argv.length == 1) {
	string filename = argv[0];
	reader = new FileReader(filename);

	// Read first five instances and print them
	cout << "\nFirst five instances from file:\n" << endl;
	instances = new Instances(reader, 1);
	instances.setClassIndex(instances.numAttributes() - 1);
	i = 0;
	while ((i < 5) && (instances.readInstance(reader))) {
	  i++;
	}
	cout << instances << endl;

	// Read all the instances in the file
	reader = new FileReader(filename);
	instances = new Instances(reader);

	// Make the last attribute be the class
	instances.setClassIndex(instances.numAttributes() - 1);

	// Print header and instances.
	cout << "\nDataset:\n" << endl;
	cout << instances << endl;
	cout << "\nClass index: "<<instances.classIndex() << endl;
      }

      // Test basic methods based on class index.
      cout << "\nClass name: "<<instances.classAttribute().name() << endl;
      cout << "\nClass index: "<<instances.classIndex() << endl;
      cout << "\nClass is nominal: " 
	   << instances.classAttribute().isNominal() << endl;
      cout << "\nClass is numeric: " 
	   << instances.classAttribute().isNumeric() << endl;
      cout << "\nClasses:\n" << endl;
      for (i = 0; i < instances.numClasses(); i++) {
	cout << instances.classAttribute().value(i) << endl;
      }
      cout << "\nClass values and labels of instances:\n" << endl;
      for (i = 0; i < instances.numInstances(); i++) {
	Instance inst = instances.instance(i);
	cout << inst.classValue() << "\t" << endl;
	cout << inst.toString(inst.classIndex()) << endl;
	if (instances.instance(i).classIsMissing()) {
	  cout << "\tis missing" << endl;
	} else {
	  cout << endl;
	}
      }

      // Create random weights.
      cout << "\nCreating random weights for instances." << endl;
      for (i = 0; i < instances.numInstances(); i++) {
	instances.instance(i).setWeight(random.nextDouble());
      }

      // Print all instances and their weights (and the sum of weights).
      cout << "\nInstances and their weights:\n" << endl;
      cout << instances.instancesAndWeights() << endl;
      cout << "\nSum of weights: " << endl;
      cout << instances.sumOfWeights() << endl;

      // Insert an attribute
      secondInstances = new Instances(instances);
      Attribute testAtt = new Attribute("Inserted");
      secondInstances.insertAttributeAt(testAtt, 0);
      cout << "\nSet with inserted attribute:\n" << endl;
      cout << secondInstances << endl;
      cout << "\nClass name: "
	   << secondInstances.classAttribute().name() << endl;

      // Delete the attribute
      secondInstances.deleteAttributeAt(0);
      cout << "\nSet with attribute deleted:\n" << endl;
      cout << secondInstances << endl;
      cout << "\nClass name: "
	   << secondInstances.classAttribute().name() << endl;

      // Test if headers are equal
      cout << "\nHeaders equal: "
	   << instances.equalHeaders(secondInstances) << "\n" << endl;

      // Print data in internal format.
      cout << "\nData (internal values):\n" << endl;
      for (i = 0; i < instances.numInstances(); i++) {
	for (j = 0; j < instances.numAttributes(); j++) {
	  if (instances.instance(i).isMissing(j)) {
	    cout << "? " << endl;
	  } else {
	    cout << instances.instance(i).value(j) << " " << endl;
	  }
	}
	cout << endl;
      }

      // Just print header
      cout << "\nEmpty dataset:\n" << endl;
      empty = new Instances(instances, 0);
      cout << empty << endl;
      cout << "\nClass name: "<<empty.classAttribute().name() << endl;

      // Create copy and rename an attribute and a value (if possible)
      if (empty.classAttribute().isNominal()) {
	Instances copy = new Instances(empty, 0);
	copy.renameAttribute(copy.classAttribute(), "new_name");
	copy.renameAttributeValue(copy.classAttribute(),
				  copy.classAttribute().value(0),
				  "new_val_name");
	cout << "\nDataset with names changed:\n" << copy << endl;
	cout << "\nOriginal dataset:\n" << empty << endl;
      }

      // Create and prints subset of instances.
      start = instances.numInstances() / 4;
      num = instances.numInstances() / 2;
      cout << "\nSubset of dataset: " << endl;
      cout << num << " instances from " << (start + 1)
	   << ". instance" << endl;
      secondInstances = new Instances(instances, start, num);
      cout << "\nClass name: "
	   << secondInstances.classAttribute().name() << endl;

      // Print all instances and their weights (and the sum of weights).
      cout << "\nInstances and their weights:\n" << endl;
      cout << secondInstances.instancesAndWeights() << endl;
      cout << "\nSum of weights: " << endl;
      cout << secondInstances.sumOfWeights() << endl;

      // Create and print training and test sets for 3-fold
      // cross-validation.
      cout << "\nTrain and test folds for 3-fold CV:" << endl;
      if (instances.classAttribute().isNominal()) {
	instances.stratify(3);
      }
      for (j = 0; j < 3; j++) {
        train = instances.trainCV(3,j, new Random(1));
	test = instances.testCV(3,j);

	// Print all instances and their weights (and the sum of weights).
	cout << "\nTrain: " << endl;
	cout << "\nInstances and their weights:\n" << endl;
	cout << train.instancesAndWeights() << endl;
	cout << "\nSum of weights: " << endl;
	cout << train.sumOfWeights() << endl;
	cout << "\nClass name: " << train.classAttribute().name() << endl;
	cout << "\nTest: " << endl;
	cout << "\nInstances and their weights:\n" << endl;
	cout << test.instancesAndWeights() << endl;
	cout << "\nSum of weights: " << endl;
	cout << test.sumOfWeights() << endl;
	cout << "\nClass name: " << test.classAttribute().name() << endl;
      }

      // Randomize instances and print them.
      cout << "\nRandomized dataset:" << endl;
      instances.randomize(random);

      // Print all instances and their weights (and the sum of weights).
      cout << "\nInstances and their weights:\n" << endl;
      cout << instances.instancesAndWeights() << endl;
      cout << "\nSum of weights: " << endl;
      cout << instances.sumOfWeights() << endl;

      // Sort instances according to first attribute and
      // print them.
      cout << "\nInstances sorted according to first attribute:\n " << endl;
      instances.sort(0);

      // Print all instances and their weights (and the sum of weights).
      cout << "\nInstances and their weights:\n" << endl;
      cout << instances.instancesAndWeights() << endl;
      cout << "\nSum of weights: " << endl;
      cout << instances.sumOfWeights() << endl;
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

/**
 * Main method for this class. The following calls are possible:
 * <ul>
 *   <li>
 *     <code>weka.core.Instances</code> help<br/>
 *     prints a short list of possible commands.
 *   </li>
 *   <li>
 *     <code>weka.core.Instances</code> &lt;filename&gt;<br/>
 *     prints a summary of a set of instances.
 *   </li>
 *   <li>
 *     <code>weka.core.Instances</code> merge &lt;filename1&gt; &lt;filename2&gt;<br/>
 *     merges the two datasets (must have same number of instances) and
 *     outputs the results on stdout.
 *   </li>
 *   <li>
 *     <code>weka.core.Instances</code> append &lt;filename1&gt; &lt;filename2&gt;<br/>
 *     appends the second dataset to the first one (must have same headers) and
 *     outputs the results on stdout.
 *   </li>
 *   <li>
 *     <code>weka.core.Instances</code> headers &lt;filename1&gt; &lt;filename2&gt;<br/>
 *     Compares the headers of the two datasets and prints whether they match
 *     or not.
 *   </li>
 *   <li>
 *     <code>weka.core.Instances</code> randomize &lt;seed&gt; &lt;filename&gt;<br/>
 *     randomizes the dataset with the given seed and outputs the result on stdout.
 *   </li>
 * </ul>
 *
 * @param args 	the commandline parameters
 */
void main(int argc, char* argv[]) {

  try {
    Instances i;
    // read from stdin and print statistics
    if (args.length == 0) {
      DataSource source = new DataSource(System.in);
      i = source.getDataSet();
      cout << i.toSummaryString() << endl;
    }
    // read file and print statistics
    else if ((args.length == 1) && (!args[0].equals("-h")) && (!args[0].equals("help"))) {
      DataSource source = new DataSource(args[0]);
      i = source.getDataSet();
      cout << i.toSummaryString() << endl;
    }
    // read two files, merge them and print result to stdout
    else if ((args.length == 3) && (args[0].toLowerCase().equals("merge"))) {
      DataSource source1 = new DataSource(args[1]);
      DataSource source2 = new DataSource(args[2]);
      i = Instances.mergeInstances(source1.getDataSet(), source2.getDataSet());
      cout << i << endl;
    }
    // read two files, append them and print result to stdout
    else if ((args.length == 3) && (args[0].toLowerCase().equals("append"))) {
      DataSource source1 = new DataSource(args[1]);
      DataSource source2 = new DataSource(args[2]);
      if (!source1.getStructure().equalHeaders(source2.getStructure()))
	throw Exception("The two datasets have different headers!");
      Instances structure = source1.getStructure();
      cout << source1.getStructure() << endl;
      while (source1.hasMoreElements(structure))
	cout << source1.nextElement(structure) << endl;
      structure = source2.getStructure();
      while (source2.hasMoreElements(structure))
	cout << source2.nextElement(structure) << endl;
    }
    // read two files and compare their headers
    else if ((args.length == 3) && (args[0].toLowerCase().equals("headers"))) {
      DataSource source1 = new DataSource(args[1]);
      DataSource source2 = new DataSource(args[2]);
      if (source1.getStructure().equalHeaders(source2.getStructure()))
	cout << "Headers match" << endl;
      else
	cout << "Headers don't match" << endl;
    }
    // read file and seed value, randomize data and print result to stdout
    else if ((args.length == 3) && (args[0].toLowerCase().equals("randomize"))) {
      DataSource source = new DataSource(args[2]);
      i = source.getDataSet();
      i.randomize(new Random(Integer.parseInt(args[1])));
      System.out.println(i << endl;
    }
    // wrong parameters
    else {
      cout << "\nUsage:\n" 
	   << "\tweka.core.Instances help\n" 
	   << "\tweka.core.Instances <filename>\n"
	   << "\tweka.core.Instances merge <filename1> <filename2>\n"
	   << "\tweka.core.Instances append <filename1> <filename2>\n"
	   << "\tweka.core.Instances headers <filename1> <filename2>\n"
	   << "\tweka.core.Instances randomize <seed> <filename>\n"
	   << endl;
    }
  }
  catch (Exception ex) {
    ex.printStackTrace();
    cout << ex.getMessage() << endl;
  }
}
