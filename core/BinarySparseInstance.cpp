#include "BinarySparseInstance.hpp"

BinarySparseInstance::BinarySparseInstance(Instance instance) {
    
    m_Weight = instance.m_Weight;
    m_Dataset = NULL;
    m_NumAttributes = instance.numAttributes();
    if (instance instanceof SparseInstance) {
      m_AttValues = NULL;
      m_Indices = ((SparseInstance)instance).m_Indices;
    } else {
      int[] tempIndices = new int[instance.numAttributes()];
      int vals = 0;
      for (int i = 0; i < instance.numAttributes(); i++) {
	if (instance.value(i) != 0) {
	  tempIndices[vals] = i;
	  vals++;
	}
      }
      m_AttValues = NULL;
      m_Indices = new int[vals];
      System.arraycopy(tempIndices, 0, m_Indices, 0, vals);
    }
  }
  
BinarySparseInstance::BinarySparseInstance(double weight, double[] attValues) {
    
    m_Weight = weight;
    m_Dataset = NULL;
    m_NumAttributes = attValues.length;
    int[] tempIndices = new int[m_NumAttributes];
    int vals = 0;
    for (int i = 0; i < m_NumAttributes; i++) {
      if (attValues[i] != 0) {
	tempIndices[vals] = i;
	vals++;
      }
    }
    m_AttValues = NULL;
    m_Indices = new int[vals];
    System.arraycopy(tempIndices, 0, m_Indices, 0, vals);
  }
  
BinarySparseInstance::BinarySparseInstance(int numAttributes) {
    
    m_AttValues = NULL;
    m_NumAttributes = numAttributes;
    m_Indices = new int[numAttributes];
    for (int i = 0; i < m_Indices.length; i++) {
      m_Indices[i] = i;
    }
    m_Weight = 1;
    m_Dataset = NULL;
  }

Instance BinarySparseInstance::mergeInstance(Instance inst) {

    int [] indices = new int [numValues() + inst.numValues()];

    int m = 0;
    for (int j = 0; j < numValues(); j++) {
      indices[m++] = index(j);
    }
    for (int j = 0; j < inst.numValues(); j++) {
      if (inst.valueSparse(j) != 0) {
        indices[m++] = numAttributes() + inst.index(j);
      }
    }

    if (m != indices.length) {
      // Need to truncate
      int [] newInd = new int [m];
      System.arraycopy(indices, 0, newInd, 0, m);
      indices = newInd;
    }
    return new BinarySparseInstance(1.0, indices, numAttributes() +
                                    inst.numAttributes());
  }

void BinarySparseInstance::setValue(int attIndex, double value) {

    int index = locateIndex(attIndex);
    
    if ((index >= 0) && (m_Indices[index] == attIndex)) {
      if (value == 0) {
	int[] tempIndices = new int[m_Indices.length - 1];
	System.arraycopy(m_Indices, 0, tempIndices, 0, index);
	System.arraycopy(m_Indices, index + 1, tempIndices, index, 
			 m_Indices.length - index - 1);
	m_Indices = tempIndices;
      }
    } else {
      if (value != 0) {
	int[] tempIndices = new int[m_Indices.length + 1];
	System.arraycopy(m_Indices, 0, tempIndices, 0, index + 1);
	tempIndices[index + 1] = attIndex;
	System.arraycopy(m_Indices, index + 1, tempIndices, index + 2, 
			 m_Indices.length - index - 1);
	m_Indices = tempIndices;
      }
    }
  }

void BinarySparseInstance::setValueSparse(int indexOfIndex, double value) {

    if (value == 0) {
      int[] tempIndices = new int[m_Indices.length - 1];
      System.arraycopy(m_Indices, 0, tempIndices, 0, indexOfIndex);
      System.arraycopy(m_Indices, indexOfIndex + 1, tempIndices, indexOfIndex, 
		       m_Indices.length - indexOfIndex - 1);
      m_Indices = tempIndices;
    }
  }

double[] BinarySparseInstance::toDoubleArray() {

    double[] newValues = new double[m_NumAttributes];
    for (int i = 0; i < m_Indices.length; i++) {
      newValues[m_Indices[i]] = 1.0;
    }
    return newValues;
  }

string BinarySparseInstance::toString() {

    StringBuffer text = new StringBuffer();
    
    text.append('{');
    for (int i = 0; i < m_Indices.length; i++) {
      if (i > 0) {
        text.append(",");
      }
      if (m_Dataset == NULL) {
        text.append(m_Indices[i] + " 1");
      } else {
        if (m_Dataset.attribute(m_Indices[i]).isNominal() || 
            m_Dataset.attribute(m_Indices[i]).isString()) {
          text.append(m_Indices[i] + " " +
                      Utils.quote(m_Dataset.attribute(m_Indices[i]).
                                  value(1)));
        } else {
          text.append(m_Indices[i] + " 1");
        }
      }
    }
    text.append('}');
    if (m_Weight != 1.0) {
      text.append(",{" + Utils.doubleToString(m_Weight, 6) + "}");
    }
    return text.toString();
  }

double BinarySparseInstance::value(int attIndex) {

    int index = locateIndex(attIndex);
    if ((index >= 0) && (m_Indices[index] == attIndex)) {
      return 1.0;
    } else {
      return 0.0;
    }
  }  

void BinarySparseInstance::forceDeleteAttributeAt(int position) {

    int index = locateIndex(position);

    m_NumAttributes--;
    if ((index >= 0) && (m_Indices[index] == position)) {
      int[] tempIndices = new int[m_Indices.length - 1];
      System.arraycopy(m_Indices, 0, tempIndices, 0, index);
      for (int i = index; i < m_Indices.length - 1; i++) {
	tempIndices[i] = m_Indices[i + 1] - 1;
      }
      m_Indices = tempIndices;
    } else {
      int[] tempIndices = new int[m_Indices.length];
      System.arraycopy(m_Indices, 0, tempIndices, 0, index + 1);
      for (int i = index + 1; i < m_Indices.length - 1; i++) {
	tempIndices[i] = m_Indices[i] - 1;
      }
      m_Indices = tempIndices;
    }
  }

void BinarySparseInstance::forceInsertAttributeAt(int position)  {

    int index = locateIndex(position);

    m_NumAttributes++;
    if ((index >= 0) && (m_Indices[index] == position)) {
      int[] tempIndices = new int[m_Indices.length + 1];
      System.arraycopy(m_Indices, 0, tempIndices, 0, index);
      tempIndices[index] = position;
      for (int i = index; i < m_Indices.length; i++) {
	tempIndices[i + 1] = m_Indices[i] + 1;
      }
      m_Indices = tempIndices;
    } else {
      int[] tempIndices = new int[m_Indices.length + 1];
      System.arraycopy(m_Indices, 0, tempIndices, 0, index + 1);
      tempIndices[index + 1] = position;
      for (int i = index + 1; i < m_Indices.length; i++) {
	tempIndices[i + 1] = m_Indices[i] + 1;
      }
      m_Indices = tempIndices;
    }
  }

void BinarySparseInstance::main(String[] options) {

  try {

    // Create numeric attributes "length" and "weight"
    Attribute length = new Attribute("length");
    Attribute weight = new Attribute("weight");
      
    // Create vector to hold nominal values "first", "second", "third" 
    FastVector my_nominal_values = new FastVector(3); 
    my_nominal_values.addElement("first"); 
    my_nominal_values.addElement("second"); 
      
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
    BinarySparseInstance inst = new BinarySparseInstance(3);
      
    // Set instance's values for the attributes "length", "weight", and "position"
    inst.setValue(length, 5.3);
    inst.setValue(weight, 300);
    inst.setValue(position, "first");
      
    // Set instance's dataset to be the dataset "race"
    inst.setDataset(race);
      
    // Print the instance
    System.out.println("The instance: " + inst);
      
    // Print the first attribute
    System.out.println("First attribute: " + inst.attribute(0));
      
    // Print the class attribute
    System.out.println("Class attribute: " + inst.classAttribute());
      
    // Print the class index
    System.out.println("Class index: " + inst.classIndex());
      
    // Say if class is missing
    System.out.println("Class is missing: " + inst.classIsMissing());
      
    // Print the instance's class value in internal format
    System.out.println("Class value (internal format): " + inst.classValue());
      
    // Print a shallow copy of this instance
    SparseInstance copy = (SparseInstance) inst.copy();
    System.out.println("Shallow copy: " + copy);
      
    // Set dataset for shallow copy
    copy.setDataset(inst.dataset());
    System.out.println("Shallow copy with dataset set: " + copy);

    // Print out all values in internal format
    System.out.print("All stored values in internal format: ");
    for (int i = 0; i < inst.numValues(); i++) {
      if (i > 0) {
	System.out.print(",");
      }
      System.out.print(inst.valueSparse(i));
    }
    System.out.println();

    // Set all values to zero
    System.out.print("All values set to zero: ");
    while (inst.numValues() > 0) {
      inst.setValueSparse(0, 0);
    }
    for (int i = 0; i < inst.numValues(); i++) {
      if (i > 0) {
	System.out.print(",");
      }
      System.out.print(inst.valueSparse(i));
    }
    System.out.println();

    // Set all values to one
    System.out.print("All values set to one: ");
    for (int i = 0; i < inst.numAttributes(); i++) {
      inst.setValue(i, 1);
    }
    for (int i = 0; i < inst.numValues(); i++) {
      if (i > 0) {
	System.out.print(",");
      }
      System.out.print(inst.valueSparse(i));
    }
    System.out.println();

    // Unset dataset for copy, delete first attribute, and insert it again
    copy.setDataset(NULL);
    copy.deleteAttributeAt(0);
    copy.insertAttributeAt(0);
    copy.setDataset(inst.dataset());
    System.out.println("Copy with first attribute deleted and inserted: " + copy); 

    // Same for second attribute
    copy.setDataset(NULL);
    copy.deleteAttributeAt(1);
    copy.insertAttributeAt(1);
    copy.setDataset(inst.dataset());
    System.out.println("Copy with second attribute deleted and inserted: " + copy); 

    // Same for last attribute
    copy.setDataset(NULL);
    copy.deleteAttributeAt(2);
    copy.insertAttributeAt(2);
    copy.setDataset(inst.dataset());
    System.out.println("Copy with third attribute deleted and inserted: " + copy); 
      
    // Enumerate attributes (leaving out the class attribute)
    System.out.println("Enumerating attributes (leaving out class):");
    Enumeration enu = inst.enumerateAttributes();
    while (enu.hasMoreElements()) {
      Attribute att = (Attribute) enu.nextElement();
      System.out.println(att);
    }
      
    // Headers are equivalent?
    System.out.println("Header of original and copy equivalent: " +
		       inst.equalHeaders(copy));

    // Test for missing values
    System.out.println("Length of copy missing: " + copy.isMissing(length));
    System.out.println("Weight of copy missing: " + copy.isMissing(weight.index()));
    System.out.println("Length of copy missing: " + 
		       Instance.isMissingValue(copy.value(length)));
    System.out.println("Missing value coded as: " + Instance.missingValue());

    // Prints number of attributes and classes
    System.out.println("Number of attributes: " + copy.numAttributes());
    System.out.println("Number of classes: " + copy.numClasses());

    // Replace missing values
    double[] meansAndModes = {2, 3, 0};
    copy.replaceMissingValues(meansAndModes);
    System.out.println("Copy with missing value replaced: " + copy);

    // Setting and getting values and weights
    copy.setClassMissing();
    System.out.println("Copy with missing class: " + copy);
    copy.setClassValue(0);
    System.out.println("Copy with class value set to first value: " + copy);
    copy.setClassValue("second");
    System.out.println("Copy with class value set to \"second\": " + copy);
    copy.setMissing(1);
    System.out.println("Copy with second attribute set to be missing: " + copy);
    copy.setMissing(length);
    System.out.println("Copy with length set to be missing: " + copy);
    copy.setValue(0, 0);
    System.out.println("Copy with first attribute set to 0: " + copy);
    copy.setValue(weight, 1);
    System.out.println("Copy with weight attribute set to 1: " + copy);
    copy.setValue(position, "second");
    System.out.println("Copy with position set to \"second\": " + copy);
    copy.setValue(2, "first");
    System.out.println("Copy with last attribute set to \"first\": " + copy);
    System.out.println("Current weight of instance copy: " + copy.weight());
    copy.setWeight(2);
    System.out.println("Current weight of instance copy (set to 2): " + copy.weight());
    System.out.println("Last value of copy: " + copy.toString(2));
    System.out.println("Value of position for copy: " + copy.toString(position));
    System.out.println("Last value of copy (internal format): " + copy.value(2));
    System.out.println("Value of position for copy (internal format): " + 
		       copy.value(position));
  } catch (Exception e) {
    e.printStackTrace();
  }
}
  
#endif
