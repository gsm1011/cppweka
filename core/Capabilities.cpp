#include <list>
#include <iterator>
#include <vector>
#include <hashmap>

#include "Capabilities.hpp"

// import weka.core.converters.ConverterUtils.DataSource;

// import java.util.Collections;
// import java.util.Properties;

Capabilities::Capabilities(CapabilitiesHandler owner) {
    super();

    setOwner(owner);
    m_Capabilities = new HashSet();
    m_Dependencies = new HashSet();

    // load properties
    if (PROPERTIES == NULL) {
      try {
        PROPERTIES = Utils.readProperties(PROPERTIES_FILE);
      }
      catch (Exception e) {
	e.printStackTrace();
	PROPERTIES = new Properties();
      }
    }
    
    m_Test                       = Boolean.parseBoolean(PROPERTIES.getProperty("Test", "true"));
    m_InstancesTest              = Boolean.parseBoolean(PROPERTIES.getProperty("InstancesTest", "true")) && m_Test;
    m_AttributeTest              = Boolean.parseBoolean(PROPERTIES.getProperty("AttributeTest", "true")) && m_Test;
    m_MissingValuesTest          = Boolean.parseBoolean(PROPERTIES.getProperty("MissingValuesTest", "true")) && m_Test;
    m_MissingClassValuesTest     = Boolean.parseBoolean(PROPERTIES.getProperty("MissingClassValuesTest", "true")) && m_Test;
    m_MinimumNumberInstancesTest = Boolean.parseBoolean(PROPERTIES.getProperty("MinimumNumberInstancesTest", "true")) && m_Test;
  }
  
void Capabilities::assign(Capabilities c) {
    for (Capability cap: Capability.values()) {
      // capability
      if (c.handles(cap))
        enable(cap);
      else
	disable(cap);
      // dependency
      if (c.hasDependency(cap))
        enableDependency(cap);
      else
	disableDependency(cap);
    }

    setMinimumNumberInstances(c.getMinimumNumberInstances());
  }

void Capabilities::and(Capabilities c) {
    for (Capability cap: Capability.values()) {
      // capability
      if (handles(cap) && c.handles(cap))
        m_Capabilities.add(cap);
      else
        m_Capabilities.remove(cap);
      // dependency
      if (hasDependency(cap) && c.hasDependency(cap))
        m_Dependencies.add(cap);
      else
        m_Dependencies.remove(cap);
    }
    
    // minimum number of instances that both handlers need at least to work
    if (c.getMinimumNumberInstances() > getMinimumNumberInstances())
      setMinimumNumberInstances(c.getMinimumNumberInstances());
  }

void Capabilities::or(Capabilities c) {
    for (Capability cap: Capability.values()) {
      // capability
      if (handles(cap) || c.handles(cap))
        m_Capabilities.add(cap);
      else
        m_Capabilities.remove(cap);
      // dependency
      if (hasDependency(cap) || c.hasDependency(cap))
        m_Dependencies.add(cap);
      else
        m_Dependencies.remove(cap);
    }
    
    if (c.getMinimumNumberInstances() < getMinimumNumberInstances())
      setMinimumNumberInstances(c.getMinimumNumberInstances());
  }
  
bool Capabilities::supports(Capabilities c) {
    bool	result;
    
    result = true;
    
    for (Capability cap: Capability.values()) {
      if (c.handles(cap) && !handles(cap)) {
	result = false;
	break;
      }
    }

    return result;
  }
  
bool Capabilities::supportsMaybe(Capabilities c) {
    bool	result;
    
    result = true;
    
    for (Capability cap: Capability.values()) {
      if (c.handles(cap) && !(handles(cap) || hasDependency(cap))) {
	result = false;
	break;
      }
    }

    return result;
  }

void Capabilities::enable(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      enable(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      enable(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      enable(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      enable(Capability.BINARY_CLASS);
    }

    m_Capabilities.add(c);
  }
  
void Capabilities::enableDependency(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      enableDependency(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      enableDependency(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      enableDependency(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      enableDependency(Capability.BINARY_CLASS);
    }

    m_Dependencies.add(c);
  }
  
void Capabilities::enableAllClasses() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	enable(cap);
    }
  }
  
void Capabilities::enableAllClassDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	enableDependency(cap);
    }
  }
  
void Capabilities::enableAllAttributes() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	enable(cap);
    }
  }

void Capabilities::enableAllAttributeDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	enableDependency(cap);
    }
  }
  
void Capabilities::enableAll() {
    enableAllAttributes();
    enableAllAttributeDependencies();
    enableAllClasses();
    enableAllClassDependencies();
    enable(Capability.MISSING_VALUES);
    enable(Capability.MISSING_CLASS_VALUES);
  }

void Capabilities::disable(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      disable(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      disable(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      disable(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      disable(Capability.BINARY_CLASS);
    }
    else if (c == Capability.BINARY_CLASS) {
      disable(Capability.UNARY_CLASS);
    }
    else if (c == Capability.UNARY_CLASS) {
      disable(Capability.EMPTY_NOMINAL_CLASS);
    }

    m_Capabilities.remove(c);
  }

void Capabilities::disableDependency(Capability c) {
    // attributes
    if (c == Capability.NOMINAL_ATTRIBUTES) {
      disableDependency(Capability.BINARY_ATTRIBUTES);
    }
    else if (c == Capability.BINARY_ATTRIBUTES) {
      disableDependency(Capability.UNARY_ATTRIBUTES);
    }
    else if (c == Capability.UNARY_ATTRIBUTES) {
      disableDependency(Capability.EMPTY_NOMINAL_ATTRIBUTES);
    }
    // class
    else if (c == Capability.NOMINAL_CLASS) {
      disableDependency(Capability.BINARY_CLASS);
    }
    else if (c == Capability.BINARY_CLASS) {
      disableDependency(Capability.UNARY_CLASS);
    }
    else if (c == Capability.UNARY_CLASS) {
      disableDependency(Capability.EMPTY_NOMINAL_CLASS);
    }

    m_Dependencies.remove(c);
  }
  
void Capabilities::disableAllClasses() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	disable(cap);
    }
  }
  
void Capabilities::disableAllClassDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isClass())
	disableDependency(cap);
    }
  }
  
void Capabilities::disableAllAttributes() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	disable(cap);
    }
  }
  

void Capabilities::disableAllAttributeDependencies() {
    for (Capability cap: Capability.values()) {
      if (cap.isAttribute())
	disableDependency(cap);
    }
  }
  
void Capabilities::disableAll() {
    disableAllAttributes();
    disableAllAttributeDependencies();
    disableAllClasses();
    disableAllClassDependencies();
    disable(Capability.MISSING_VALUES);
    disable(Capability.MISSING_CLASS_VALUES);
    disable(Capability.NO_CLASS);
  }
  
Capabilities Capabilities::getClassCapabilities() {
    Capabilities	result;
    
    result = new Capabilities(getOwner());
    
    for (Capability cap: Capability.values()) {
      if (cap.isClassCapability()) {
	if (handles(cap))
	  result.m_Capabilities.add(cap);
      }
    }
    
    return result;
  }
  
Capabilities Capabilities::getAttributeCapabilities() {
    Capabilities	result;
    
    result = new Capabilities(getOwner());
    
    for (Capability cap: Capability.values()) {
      if (cap.isAttributeCapability()) {
	if (handles(cap))
	  result.m_Capabilities.add(cap);
      }
    }
    
    return result;
  }
  
Capabilities Capabilities::getOtherCapabilities() {
    Capabilities	result;
    
    result = new Capabilities(getOwner());
    
    for (Capability cap: Capability.values()) {
      if (cap.isOtherCapability()) {
	if (handles(cap))
	  result.m_Capabilities.add(cap);
      }
    }
    
    return result;
  }

string Capabilities::createMessage(string msg) {
    String	result;
    
    result = "";
    
    if (getOwner() != NULL)
      result = getOwner().getClass().getName();
    else
      result = "<anonymous>";
      
    result += ": " + msg;
    
    return result;
  }
  
bool Capabilities::test(Attribute att) {
    return test(att, false);
  }
  
bool Capabilities::test(Attribute att, bool isClass) {
    bool		result;
    Capability		cap;
    Capability		capBinary;
    Capability		capUnary;
    Capability		capEmpty;
    String		errorStr;
    
    result = true;
    
    // shall we test the data?
    if (!m_AttributeTest)
      return result;

    // for exception
    if (isClass)
      errorStr  = "class";
    else
      errorStr  = "attributes";
    
    switch (att.type()) {
      case Attribute.NOMINAL:
	if (isClass) {
	  cap       = Capability.NOMINAL_CLASS;
	  capBinary = Capability.BINARY_CLASS;
	  capUnary  = Capability.UNARY_CLASS;
	  capEmpty  = Capability.EMPTY_NOMINAL_CLASS;
	}
	else {
	  cap       = Capability.NOMINAL_ATTRIBUTES;
	  capBinary = Capability.BINARY_ATTRIBUTES;
	  capUnary  = Capability.UNARY_ATTRIBUTES;
	  capEmpty  = Capability.EMPTY_NOMINAL_ATTRIBUTES;
	}
	
        if (handles(cap) && (att.numValues() > 2))
          break;
        else if (handles(capBinary) && (att.numValues() == 2))
          break;
        else if (handles(capUnary) && (att.numValues() == 1))
          break;
        else if (handles(capEmpty) && (att.numValues() == 0))
          break;

        if (att.numValues() == 0) {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle empty nominal " + errorStr + "!"));
          result = false;
        }
        if (att.numValues() == 1) {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle unary " + errorStr + "!"));
          result = false;
        }
        else if (att.numValues() == 2) {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle binary " + errorStr + "!"));
          result = false;
        }
        else {
          m_FailReason = new UnsupportedAttributeTypeException(
              createMessage("Cannot handle multi-valued nominal " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.NUMERIC:
	if (isClass)
	  cap = Capability.NUMERIC_CLASS;
	else
	  cap = Capability.NUMERIC_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle numeric " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.DATE:
	if (isClass)
	  cap = Capability.DATE_CLASS;
	else
	  cap = Capability.DATE_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle date " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.STRING:
	if (isClass)
	  cap = Capability.STRING_CLASS;
	else
	  cap = Capability.STRING_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle string " + errorStr + "!"));
          result = false;
        }
        break;

      case Attribute.RELATIONAL:
	if (isClass)
	  cap = Capability.RELATIONAL_CLASS;
	else
	  cap = Capability.RELATIONAL_ATTRIBUTES;
	
        if (!handles(cap)) {
          m_FailReason = new UnsupportedAttributeTypeException(
                              createMessage("Cannot handle relational " + errorStr + "!"));
          result = false;
        }
        // attributes in the relation of this attribute must be tested
        // separately with a different Capabilites object
        break;

      default:
        m_FailReason = new UnsupportedAttributeTypeException(
                            createMessage("Cannot handle unknown attribute type '" 
                                        + att.type() + "'!"));
        result = false;
    }
    
    return result;
  }
  
bool Capabilities::test(Instances data) {
    return test(data, 0, data.numAttributes() - 1);
  }
  
bool Capabilities::test(Instances data, int fromIndex, int toIndex) {
    int         	i;
    int         	n;
    int			m;
    Attribute   	att;
    Instance    	inst;
    bool		testClass;
    Capabilities	cap;
    bool		missing;
    Iterator		iter;
    
    // shall we test the data?
    if (!m_InstancesTest)
      return true;
    
    // no Capabilities? -> warning
    if (    (m_Capabilities.size() == 0) 
	 || ((m_Capabilities.size() == 1) && handles(Capability.NO_CLASS)) )
      System.err.println(createMessage("No capabilities set!"));
    
    // any attributes?
    if (toIndex - fromIndex < 0) {
      m_FailReason = new WekaException(
                          createMessage("No attributes!"));
      return false;
    }

    // do wee need to test the class attribute, i.e., is the class attribute
    // within the range of attributes?
    testClass =    (data.classIndex() > -1) 
    		&& (data.classIndex() >= fromIndex)
    		&& (data.classIndex() <= toIndex);
    
    // attributes
    for (i = fromIndex; i <= toIndex; i++) {
      att = data.attribute(i);
      
      // class is handled separately
      if (i == data.classIndex())
        continue;
      
      // check attribute types
      if (!test(att))
	return false;
    }

    // class
    if (!handles(Capability.NO_CLASS) && (data.classIndex() == -1)) {
      m_FailReason = new UnassignedClassException(
	  createMessage("Class attribute not set!"));
      return false;
    }
      
    // special case: no class attribute can be handled
    if (handles(Capability.NO_CLASS) && (data.classIndex() > -1)) {
      cap  = getClassCapabilities();
      cap.disable(Capability.NO_CLASS);
      iter = cap.capabilities();
      if (!iter.hasNext()) {
	m_FailReason = new WekaException(
	    createMessage("Cannot handle any class attribute!"));
	return false;
      }
    }
      
    if (testClass && !handles(Capability.NO_CLASS)) {
      att = data.classAttribute();
      if (!test(att, true))
	return false;

      // special handling of RELATIONAL class
      // TODO: store additional Capabilities for this case
      
      // missing class labels
      if (m_MissingClassValuesTest) {
	if (!handles(Capability.MISSING_CLASS_VALUES)) {
	  for (i = 0; i < data.numInstances(); i++) {
	    if (data.instance(i).classIsMissing()) {
	      m_FailReason = new WekaException(
		  createMessage("Cannot handle missing class values!"));
	      return false;
	    }
	  }
	}
	else {
	  if (m_MinimumNumberInstancesTest) {
	    int hasClass = 0;
	    
	    for (i = 0; i < data.numInstances(); i++) {
	      if (!data.instance(i).classIsMissing())
		hasClass++;
	    }
	    
	    // not enough instances with class labels?
	    if (hasClass < getMinimumNumberInstances()) {
	      m_FailReason = new WekaException(
		  createMessage("Not enough training instances with class labels (required: " 
		      + getMinimumNumberInstances() 
		      + ", provided: " 
		      + hasClass + ")!"));
	      return false;
	    }
	  }
	}
      }
    }

    // missing values
    if (m_MissingValuesTest) {
      if (!handles(Capability.MISSING_VALUES)) {
	missing = false;
	for (i = 0; i < data.numInstances(); i++) {
	  inst = data.instance(i);
	  
	  if (inst instanceof SparseInstance) {
	    for (m = 0; m < inst.numValues(); m++) {
	      n = inst.index(m);
	      
	      // out of scope?
	      if (n < fromIndex)
		continue;
	      if (n > toIndex)
		break;

	      // skip class
	      if (n == inst.classIndex())
		continue;
	      

	      if (inst.isMissing(n)) {
		missing = true;
		break;
	      }
	    }
	  }
	  else {
	    for (n = fromIndex; n <= toIndex; n++) {
	      // skip class
	      if (n == inst.classIndex())
		continue;

	      if (inst.isMissing(n)) {
		missing = true;
		break;
	      }
	    }
	  }
	  
	  if (missing) {
	    m_FailReason = new NoSupportForMissingValuesException(
		createMessage("Cannot handle missing values!"));
	    return false;
	  }
	}
      }
    }
    
    // instances
    if (m_MinimumNumberInstancesTest) {
      if (data.numInstances() < getMinimumNumberInstances()) {
	m_FailReason = new WekaException(
	    createMessage("Not enough training instances (required: " 
		+ getMinimumNumberInstances() 
		+ ", provided: " 
		+ data.numInstances() + ")!"));
	return false;
      }
    }

    // Multi-Instance? -> check structure (regardless of attribute range!)
    if (handles(Capability.ONLY_MULTIINSTANCE)) {
      // number of attributes?
      if (data.numAttributes() != 3) {
        m_FailReason = new WekaException(
                            createMessage("Incorrect Multi-Instance format, must be 'bag-id, bag, class'!"));
        return false;
      }
      
      // type of attributes and position of class?
      if (    !data.attribute(0).isNominal() 
           || !data.attribute(1).isRelationValued() 
           || (data.classIndex() != data.numAttributes() - 1) ) {
        m_FailReason = new WekaException(
            createMessage("Incorrect Multi-Instance format, must be 'NOMINAL att, RELATIONAL att, CLASS att'!"));
        return false;
      }

      // check data immediately
      if (getOwner() instanceof MultiInstanceCapabilitiesHandler) {
	MultiInstanceCapabilitiesHandler handler = (MultiInstanceCapabilitiesHandler) getOwner();
	cap = handler.getMultiInstanceCapabilities();
	bool result;
	if (data.numInstances() > 0)
	  result = cap.test(data.attribute(1).relation(0));
	else
	  result = cap.test(data.attribute(1).relation());
	
	if (!result) {
	  m_FailReason = cap.m_FailReason;
	  return false;
	}
      }
    }
    
    // passed all tests!
    return true;
  }

void Capabilities::testWithFail(Attribute att) throws Exception {
    test(att, false);
  }

void Capabilities::testWithFail(Attribute att, bool isClass) throws Exception {
    if (!test(att, isClass))
      throw m_FailReason;
  }

void Capabilities::testWithFail(Instances data, int fromIndex, int toIndex) throws Exception {
    if (!test(data, fromIndex, toIndex))
      throw m_FailReason;
  }

void Capabilities::testWithFail(Instances data) throws Exception {
    if (!test(data))
      throw m_FailReason;
  }
  
string Capabilities::toString() {
    Vector		sorted;
    StringBuffer	result;
    
    result = new StringBuffer();

    // capabilities
    sorted = new Vector(m_Capabilities);
    Collections.sort(sorted);
    result.append("Capabilities: " + sorted.toString() + "\n");

    // dependencies
    sorted = new Vector(m_Dependencies);
    Collections.sort(sorted);
    result.append("Dependencies: " + sorted.toString() + "\n");
    
    // other stuff
    result.append("min # Instance: " + getMinimumNumberInstances() + "\n");
    
    return result.toString();
  }
  
string Capabilities::toSource(string objectname) {
    return toSource(objectname, 0);
  }
    
string Capabilities::toSource(string objectname, int indent) {
    StringBuffer	result;
    String		capsName;
    String		capName;
    String		indentStr;
    int			i;
    
    result = new StringBuffer();

    capsName = Capabilities.class.getName();
    capName  = Capabilities.Capability.class.getName().replaceAll("\\$", ".");
    
    indentStr = "";
    for (i = 0; i < indent; i++)
      indentStr += " ";
    
    // object name
    result.append(indentStr + capsName + " " + objectname + " = new " + capsName + "(this);\n");
    
    List<Capability> capsList = new ArrayList<Capability>();
    bool hasNominalAtt = false;
    bool hasBinaryAtt = false;
    bool hasUnaryAtt = false;
    bool hasEmptyNomAtt = false;
    bool hasNominalClass = false;
    // capabilities
    result.append("\n");
    for (Capability cap: Capability.values()) {
      // capability
      if (handles(cap)) {
        if (cap == Capability.NOMINAL_ATTRIBUTES) {
          hasNominalAtt = true;
        }
        if (cap == Capability.NOMINAL_CLASS) {
          hasNominalClass = true;
        }
        if (cap == Capability.BINARY_ATTRIBUTES) {
          hasBinaryAtt = true;
        }
        if (cap == Capability.UNARY_ATTRIBUTES) {
          hasUnaryAtt = true;
        }
        if (cap == Capability.EMPTY_NOMINAL_ATTRIBUTES) {
          hasEmptyNomAtt = true;
        }
        capsList.add(cap);              
      }
    }
    
    for (Capability cap : capsList) {
      if ((cap == Capability.BINARY_ATTRIBUTES && hasNominalAtt) ||
          (cap == Capability.UNARY_ATTRIBUTES && hasBinaryAtt) ||
          (cap == Capability.EMPTY_NOMINAL_ATTRIBUTES && hasUnaryAtt) ||
          (cap == Capability.BINARY_CLASS && hasNominalClass)) {
        continue;
      }
      result.append(
          indentStr + objectname + ".enable(" + capName + "." + cap.name() + ");\n");
      // dependency
      if (hasDependency(cap))
        result.append(
            indentStr + objectname + ".enableDependency(" + capName + "." + cap.name() + ");\n");
    }

    // other
    result.append("\n");
    result.append(
	indentStr + objectname + ".setMinimumNumberInstances(" 
	+ getMinimumNumberInstances() + ");\n");

    result.append("\n");
    
    return result.toString();
  }
  
static Capabilities Capabilities::forInstances(Instances data) throws Exception {
    return forInstances(data, false);
  }
  
static Capabilities Capabilities::forInstances(Instances data, bool multi) throws Exception {
    Capabilities	result;
    Capabilities	multiInstance;
    int			i;
    int			n;
    int			m;
    Instance		inst;
    bool		missing;
    
    result = new Capabilities(NULL);
    
    // class
    if (data.classIndex() == -1) {
      result.enable(Capability.NO_CLASS);
    }
    else {
      switch (data.classAttribute().type()) {
	case Attribute.NOMINAL:
	  if (data.classAttribute().numValues() == 1)
	    result.enable(Capability.UNARY_CLASS);
	  else if (data.classAttribute().numValues() == 2)
	    result.enable(Capability.BINARY_CLASS);
	  else
	    result.enable(Capability.NOMINAL_CLASS);
	  break;
	  
	case Attribute.NUMERIC:
	  result.enable(Capability.NUMERIC_CLASS);
	  break;
	  
	case Attribute.STRING:
	  result.enable(Capability.STRING_CLASS);
	  break;
	  
	case Attribute.DATE:
	  result.enable(Capability.DATE_CLASS);
	  break;
	  
	case Attribute.RELATIONAL:
	  result.enable(Capability.RELATIONAL_CLASS);
	  break;
	  
	default:
	  throw UnsupportedAttributeTypeException(
	      "Unknown class attribute type '" + data.classAttribute() + "'!");
      }
      
      // missing class values
      for (i = 0; i < data.numInstances(); i++) {
	if (data.instance(i).classIsMissing()) {
	  result.enable(Capability.MISSING_CLASS_VALUES);
	  break;
	}
      }
    }
    
    // attributes
    for (i = 0; i < data.numAttributes(); i++) {
      // skip class
      if (i == data.classIndex())
	continue;

      switch (data.attribute(i).type()) {
	case Attribute.NOMINAL:
	  result.enable(Capability.UNARY_ATTRIBUTES);
	  if (data.attribute(i).numValues() == 2)
	    result.enable(Capability.BINARY_ATTRIBUTES);
	  else if (data.attribute(i).numValues() > 2)
	    result.enable(Capability.NOMINAL_ATTRIBUTES);
	  break;

	case Attribute.NUMERIC:
	  result.enable(Capability.NUMERIC_ATTRIBUTES);
	  break;
		
	case Attribute.DATE:
	  result.enable(Capability.DATE_ATTRIBUTES);
	  break;

	case Attribute.STRING:
	  result.enable(Capability.STRING_ATTRIBUTES);
	  break;
	  
	case Attribute.RELATIONAL:
	  result.enable(Capability.RELATIONAL_ATTRIBUTES);
	  break;
	  
	default:
	  throw UnsupportedAttributeTypeException(
	      "Unknown attribute type '" + data.attribute(i).type() + "'!");
      }
    }
    
    // missing values
    missing = false;
    for (i = 0; i < data.numInstances(); i++) {
      inst = data.instance(i);

      if (inst instanceof SparseInstance) {
	for (m = 0; m < inst.numValues(); m++) {
	  n = inst.index(m);

	  // skip class
	  if (n == inst.classIndex())
	    continue;

	  if (inst.isMissing(n)) {
	    missing = true;
	    break;
	  }
	}
      }
      else {
	for (n = 0; n < data.numAttributes(); n++) {
	  // skip class
	  if (n == inst.classIndex())
	    continue;

	  if (inst.isMissing(n)) {
	    missing = true;
	    break;
	  }
	}
      }

      if (missing) {
	result.enable(Capability.MISSING_VALUES);
	break;
      }
    }

    // multi-instance data?
    if (multi) {
      if (    (data.numAttributes() == 3)
	   && (data.attribute(0).isNominal())		// bag-id
	   && (data.attribute(1).isRelationValued()) 	// bag
	   && (data.classIndex() == data.numAttributes() - 1) ) {
	multiInstance = new Capabilities(NULL);
	multiInstance.or(result.getClassCapabilities());
	multiInstance.enable(Capability.NOMINAL_ATTRIBUTES);
	multiInstance.enable(Capability.RELATIONAL_ATTRIBUTES);
	multiInstance.enable(Capability.ONLY_MULTIINSTANCE);
	result.assign(multiInstance);
      }
    }
    
    return result;
  }
 
string Capabilities::getRevision() {
    return RevisionUtils.extract("$Revision: 6446 $");
  }

static void Capabilities::main(String[] args) {
  string 		tmpStr;
  String		filename;
  DataSource 		source;
  Instances 		data;
  int 		classIndex;
  Capabilities 	cap;
  Iterator		iter;

  if (args.length == 0) {
    System.out.println(
		       "\nUsage: " + Capabilities.class.getName() 
		       + " -file <dataset> [-c <class index>]\n");
    return;
  }
    
  // get parameters
  tmpStr = Utils.getOption("file", args);
  if (tmpStr.length() == 0)
    throw Exception("No file provided with option '-file'!");
  else
    filename = tmpStr;

  tmpStr = Utils.getOption("c", args);
  if (tmpStr.length() != 0) {
    if (tmpStr.equals("first"))
      classIndex = 0;
    else if (tmpStr.equals("last"))
      classIndex = -2;  // last
    else
      classIndex = Integer.parseInt(tmpStr) - 1;
  }
  else {
    classIndex = -3;  // not set
  }
    
  // load data
  source = new DataSource(filename);
  if (classIndex == -3)
    data = source.getDataSet();
  else if (classIndex == -2)
    data = source.getDataSet(source.getStructure().numAttributes() - 1);
  else
    data = source.getDataSet(classIndex);

  // determine and print capabilities
  cap = forInstances(data);
  System.out.println("File: " + filename);
  System.out.println("Class index: " + ((data.classIndex() == -1) ? "not set" : "" + (data.classIndex() + 1)));
  System.out.println("Capabilities:");
  iter = cap.capabilities();
  while (iter.hasNext())
    System.out.println("- " + iter.next());
}
  
