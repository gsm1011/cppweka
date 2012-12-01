#include "Instance.hpp"
using namespace std; 

bool Instance::hasMissingValue() {
    
  if (m_Dataset == NULL) {
    throw UnassignedDatasetException("Instance doesn't have access to a dataset!");
  }
  for (int i = 0; i < numAttributes(); i++) {
    if (i != classIndex()) {
      if (isMissing(i)) {
	return true;
      }
    }
  }
  return false;
}

Instance Instance::mergeInstance(Instance inst) {

  int m = 0;
  double [] newVals = new double[numAttributes() + inst.numAttributes()];
  for (int j = 0; j < numAttributes(); j++, m++) {
    newVals[m] = value(j);
  }
  for (int j = 0; j < inst.numAttributes(); j++, m++) {
    newVals[m] = inst.value(j);
  }
  return new Instance(1.0, newVals);
}

void Instance::replaceMissingValues(double[] array) {
	 
  if ((array == NULL) || 
      (array.length != m_AttValues.length)) {
    throw IllegalArgumentException("Unequal number of attributes!");
  }
  freshAttributeVector();
  for (int i = 0; i < m_AttValues.length; i++) {
    if (isMissing(i)) {
      m_AttValues[i] = array[i];
    }
  }
}

void Instance::setValue(int attIndex, string value) {
    
  int valIndex;

  if (m_Dataset == NULL) {
    throw UnassignedDatasetException("Instance doesn't have access to a dataset!");
  }
  if (!attribute(attIndex).isNominal() &&
      !attribute(attIndex).isString()) {
    throw IllegalArgumentException("Attribute neither nominal nor string!");
  }
  valIndex = attribute(attIndex).indexOfValue(value);
  if (valIndex == -1) {
    if (attribute(attIndex).isNominal()) {
      throw IllegalArgumentException("Value not defined for given nominal attribute!");
    } else {
      attribute(attIndex).forceAddValue(value);
      valIndex = attribute(attIndex).indexOfValue(value);
    }
  }
  setValue(attIndex, (double)valIndex); 
}

void Instance::setValue(Attribute att, string value) {

  if (!att.isNominal() &&
      !att.isString()) {
    throw IllegalArgumentException("Attribute neither nominal nor string!");
  }
  int valIndex = att.indexOfValue(value);
  if (valIndex == -1) {
    if (att.isNominal()) {
      throw IllegalArgumentException("Value not defined for given nominal attribute!");
    } else {
      att.forceAddValue(value);
      valIndex = att.indexOfValue(value);
    }
  }
  setValue(att.index(), (double)valIndex);
}

double[] Instance::toDoubleArray() {

  double[] newValues = new double[m_AttValues.length];
  System.arraycopy(m_AttValues, 0, newValues, 0, 
		   m_AttValues.length);
  return newValues;
}

string Instance::toString() {

  StringBuffer text = new StringBuffer();
    
  for (int i = 0; i < m_AttValues.length; i++) {
    if (i > 0) text.append(",");
    text.append(toString(i));
  }

  if (m_Weight != 1.0) {
    text.append(",{" + Utils.doubleToString(m_Weight, 6) + "}");
  }

  return text.toString();
}


/**
 * Returns the description of one value of the instance as a 
 * string. If the instance doesn't have access to a dataset, it 
 * returns the internal floating-point value. Quotes string
 * values that contain whitespace characters, or if they
 * are a question mark.
 *
 * @param attIndex the attribute's index
 * @return the value's description as a string
 */
string Instance::toString(int attIndex) {

  StringBuffer text = new StringBuffer();
   
  if (isMissing(attIndex)) {
    text.append("?");
  } else {
    if (m_Dataset == NULL) {
      text.append(Utils.doubleToString(m_AttValues[attIndex],6));
    } else {
      switch (m_Dataset.attribute(attIndex).type()) {
      case Attribute.NOMINAL:
      case Attribute.STRING:
      case Attribute.DATE:
      case Attribute.RELATIONAL:
	text.append(Utils.quote(stringValue(attIndex)));
	break;
      case Attribute.NUMERIC:
	text.append(Utils.doubleToString(value(attIndex),6));
	break;
      default:
	throw IllegalStateException("Unknown attribute type");
      }
    }
  }
  return text.toString();
}

void Instance::forceInsertAttributeAt(int position)  {

  double[] newValues = new double[m_AttValues.length + 1];

  System.arraycopy(m_AttValues, 0, newValues, 0, position);
  newValues[position] = MISSING_VALUE;
  System.arraycopy(m_AttValues, position, newValues, 
		   position + 1, m_AttValues.length - position);
  m_AttValues = newValues;
}

void main(int argc, char* argv[]) {

  try {

    // Create numeric attributes "length" and "weight"
    Attribute length = new Attribute("length");
    Attribute weight = new Attribute("weight");
      
    // Create vector to hold nominal values "first", "second", "third" 
    FastVector my_nominal_values = new FastVector(3); 
    my_nominal_values.addElement("first"); 
    my_nominal_values.addElement("second"); 
    my_nominal_values.addElement("third"); 
      
    // Create nominal attribute "position" 
    Attribute position = new Attribute("position", my_nominal_values);
      
    // Create vector of the above attributes 
    FastVector attributes = new FastVector(3);
    attributes.addElement(length);
    attributes.addElement(weight);
    attributes.addElement(position);
      
    // Create the empty dataset "race" with above attributes
    Instances race = new Instances("race", attributes, 0);
      
    // Make position the class attribute
    race.setClassIndex(position.index());
      
    // Create empty instance with three attribute values
    Instance inst = new Instance(3);
      
    // Set instance's values for the attributes "length", "weight", and "position"
    inst.setValue(length, 5.3);
    inst.setValue(weight, 300);
    inst.setValue(position, "first");
      
    // Set instance's dataset to be the dataset "race"
    inst.setDataset(race);
      
    // Print the instance
    cout << "The instance: " << inst << endl;
      
    // Print the first attribute
    cout << "First attribute: " << inst.attribute(0) << endl;
      
    // Print the class attribute
    cout << "Class attribute: " << inst.classAttribute() << endl;
      
    // Print the class index
    cout << "Class index: " << inst.classIndex() << endl;
      
    // Say if class is missing
    cout << "Class is missing: " << inst.classIsMissing() << endl;
      
    // Print the instance's class value in internal format
    cout << "Class value (internal format): " << inst.classValue() << endl;
      
    // Print a shallow copy of this instance
    Instance copy = (Instance) inst.copy();
    cout << "Shallow copy: " << copy << endl;
      
    // Set dataset for shallow copy
    copy.setDataset(inst.dataset());
    cout << "Shallow copy with dataset set: " << copy << endl;
      
    // Unset dataset for copy, delete first attribute, and insert it again
    copy.setDataset(NULL);
    copy.deleteAttributeAt(0);
    copy.insertAttributeAt(0);
    copy.setDataset(inst.dataset());
    cout << "Copy with first attribute deleted and inserted: " 
	 << copy << endl; 
      
    // Enumerate attributes (leaving out the class attribute)
    cout << "Enumerating attributes (leaving out class):" << endl;
    Enumeration enu = inst.enumerateAttributes();
    while (enu.hasMoreElements()) {
      Attribute att = (Attribute) enu.nextElement();
      cout << att << endl;
    }
      
    // Headers are equivalent?
    cout << "Header of original and copy equivalent: " 
	 << inst.equalHeaders(copy) << endl;

    // Test for missing values
    cout << "Length of copy missing: " << copy.isMissing(length) << endl;
    cout << "Weight of copy missing: " 
	 << copy.isMissing(weight.index()) << endl;
    cout << "Length of copy missing: " 
	 << Instance.isMissingValue(copy.value(length)) << endl;
    cout << "Missing value coded as: " << Instance.missingValue() << endl;

    // Prints number of attributes and classes
    cout << "Number of attributes: " << copy.numAttributes() << endl;
    cout << "Number of classes: " << copy.numClasses() << endl;

    // Replace missing values
    double[] meansAndModes = {2, 3, 0};
    copy.replaceMissingValues(meansAndModes);
    cout << "Copy with missing value replaced: " << copy << endl;

    // Setting and getting values and weights
    copy.setClassMissing();
    cout << "Copy with missing class: " << copy << endl;
    copy.setClassValue(0);
    cout << "Copy with class value set to first value: " << copy << endl;
    copy.setClassValue("third");
    cout << "Copy with class value set to \"third\": " 
	 << copy << endl;
    copy.setMissing(1);
    cout << "Copy with second attribute set to be missing: " 
	 << copy << endl;
    copy.setMissing(length);
    cout << "Copy with length set to be missing: " << copy << endl;
    copy.setValue(0, 0);
    cout << "Copy with first attribute set to 0: " << copy << endl;
    copy.setValue(weight, 1);
    cout << "Copy with weight attribute set to 1: " << copy << endl;
    copy.setValue(position, "second");
    cout << "Copy with position set to \"second\": " << copy << endl;
    copy.setValue(2, "first");
    cout << "Copy with last attribute set to \"first\": " << copy << endl;
    cout << "Current weight of instance copy: " << copy.weight() << endl;
    copy.setWeight(2);
    cout << "Current weight of instance copy (set to 2): " 
	 << copy.weight() << endl;
    cout << "Last value of copy: " << copy.toString(2) << endl;
    cout << "Value of position for copy: " 
	 << copy.toString(position) << endl;
    cout << "Last value of copy (internal format): " 
	 << copy.value(2) << endl;
    cout << "Value of position for copy (internal format): " 
	 << copy.value(position) << endl;
  } catch (Exception e) {
    e.printStackTrace();
  }
}
