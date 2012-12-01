#include "Attribute.hpp"

using namespace std; 

Attribute::Attribute(string attributeName, 
		     FastVector attributeValues,
		     ProtectedProperties metadata) {

  m_Name = attributeName;
  m_Index = -1;
  if (attributeValues == NULL) {
    m_Values = new FastVector();
    m_Hashtable = new Hashtable();
    m_Header = NULL;
    m_Type = STRING;
  } else {
    m_Values = new FastVector(attributeValues.size());
    m_Hashtable = new Hashtable(attributeValues.size());
    m_Header = NULL;
    for (int i = 0; i < attributeValues.size(); i++) {
      Object store = attributeValues.elementAt(i);
      if (((String)store).length() > STRING_COMPRESS_THRESHOLD) {
	try {
	  store = new SerializedObject(attributeValues.elementAt(i), true);
	} catch (Exception ex) {
	  cerr << "Couldn't compress nominal attribute value -"
	       << " storing uncompressed." << endl;
	}
      }
      if (m_Hashtable.containsKey(store)) {
	std::stringstream ss; 
	ss << "A nominal attribute (" << attributeName << ") cannot" 
	   << " have duplicate labels (" << store << ").";
	throw IllegalArgumentException(ss.str());
      }
      m_Values.addElement(store);
      m_Hashtable.put(store, new Integer(i));
    }
    m_Type = NOMINAL;
  }
  setMetadata(metadata);
}

/**
 * Tests if given attribute is equal to this attribute.
 *
 * @param other the Object to be compared to this attribute
 * @return true if the given attribute is equal to this attribute
 */
bool Attribute::equals(Object other) {

  if ((other == NULL) || !(other.getClass().equals(this->getClass()))) {
    return false;
  }
  Attribute att = (Attribute) other;
  if (!m_Name.equals(att.m_Name)) {
    return false;
  }
  if (isNominal() && att.isNominal()) {
    if (m_Values.size() != att.m_Values.size()) {
      return false;
    }
    for (int i = 0; i < m_Values.size(); i++) {
      if (!m_Values.elementAt(i).equals(att.m_Values.elementAt(i))) {
	return false;
      }
    }
    return true;
  } 
  if (isRelationValued() && att.isRelationValued()) {
    if (!m_Header.equalHeaders(att.m_Header)) {
      return false;
    }
    return true;
  } 
  return (type() == att.type());
}

/**
 * Returns a description of this attribute in ARFF format. Quotes
 * strings if they contain whitespace characters, or if they
 * are a question mark.
 *
 * @return a description of this attribute as a string
 */
string Attribute::toString() {
    
  StringBuffer text = new StringBuffer();
    
  text.append(ARFF_ATTRIBUTE).append(" ").append(Utils.quote(m_Name)).append(" ");
  switch (m_Type) {
  case NOMINAL:
    text.append('{');
    Enumeration enu = enumerateValues();
    while (enu.hasMoreElements()) {
      text.append(Utils.quote((String) enu.nextElement()));
      if (enu.hasMoreElements())
	text.append(',');
    }
    text.append('}');
    break;
  case NUMERIC:
    text.append(ARFF_ATTRIBUTE_NUMERIC);
    break;
  case STRING:
    text.append(ARFF_ATTRIBUTE_STRING);
    break;
  case DATE:
    text.append(ARFF_ATTRIBUTE_DATE).append(" ").append(Utils.quote(m_DateFormat.toPattern()));
    break;
  case RELATIONAL:
    text.append(ARFF_ATTRIBUTE_RELATIONAL).append("\n");
    Enumeration enm = m_Header.enumerateAttributes();
    while (enm.hasMoreElements()) {
      text.append(enm.nextElement()).append("\n");
    }
    text.append(ARFF_END_SUBRELATION).append(" ").append(Utils.quote(m_Name));
    break;
  default:
    text.append("UNKNOWN");
    break;
  }
  return text.toString();
}

void Attribute::delete(int index) {
    
  if (!isNominal() && !isString() && !isRelationValued()) 
    throw IllegalArgumentException(std::string("Can only remove value of ") +
				   "nominal, string or relation-" +
				   " valued attribute!");
  
  else {
    m_Values = (FastVector)m_Values.copy();
    m_Values.removeElementAt(index);
    if (!isRelationValued()) {
      Hashtable hash = new Hashtable(m_Hashtable.size());
      Enumeration enu = m_Hashtable.keys();
      while (enu.hasMoreElements()) {
	Object string = enu.nextElement();
	Integer valIndexObject = (Integer)m_Hashtable.get(string);
	int valIndex = valIndexObject.intValue();
	if (valIndex > index) {
	  hash.put(string, new Integer(valIndex - 1));
	} else if (valIndex < index) {
	  hash.put(string, valIndexObject);
	}
      }
      m_Hashtable = hash;
    }
  }
}

void Attribute::setValue(int index, string string) {
    
  switch (m_Type) {
  case NOMINAL:
  case STRING:
    m_Values = (FastVector)m_Values.copy();
    m_Hashtable = (Hashtable)m_Hashtable.clone();
    Object store = string;
    if (string.length() > STRING_COMPRESS_THRESHOLD) {
      try {
	store = new SerializedObject(string, true);
      } catch (Exception ex) {
	cerr << "Couldn't compress string attribute value -"
	     << " storing uncompressed." << endl;
      }
    }
    m_Hashtable.remove(m_Values.elementAt(index));
    m_Values.setElementAt(store, index);
    m_Hashtable.put(store, new Integer(index));
    break;
  default:
    throw IllegalArgumentException(std::string("Can only set values for nominal")
				   + " or string attributes!");
  }
}

/**
 * Sets the new attribute's weight
 * 
 * @param value	the new weight
 */
void Attribute::setWeight(double value) {
  Properties	props;
  Enumeration names;
  String	name;
    
  m_Weight = value;

  // generate new metadata object
  props = new Properties();
  names = m_Metadata.propertyNames();
  while (names.hasMoreElements()) {
    name = (String) names.nextElement();
    if (!name.equals("weight"))
      props.setProperty(name, m_Metadata.getProperty(name));
  }
  std::stringstream ss; 
  ss << m_Weight; 
  props.setProperty("weight", ss.str());
  m_Metadata = new ProtectedProperties(props);
}
  
/**
 * Determines whether a value lies within the bounds of the attribute.
 *
 * @param value the value to check
 * @return whether the value is in range
 */
bool Attribute::isInRange(double value) {

  // dates and missing values are a special case 
  if (m_Type == DATE || Instance.isMissingValue(value)) return true;
  if (m_Type != NUMERIC) {
    // do label range check
    int intVal = (int) value;
    if (intVal < 0 || intVal >= m_Hashtable.size()) return false;
  } else {
    // do numeric bounds check
    if (m_LowerBoundIsOpen) {
      if (value <= m_LowerBound) return false;
    } else {
      if (value < m_LowerBound) return false;
    }
    if (m_UpperBoundIsOpen) {
      if (value >= m_UpperBound) return false;
    } else {
      if (value > m_UpperBound) return false;
    }
  }
  return true;
}

void Attribute::setMetadata(ProtectedProperties metadata) {
    
  m_Metadata = metadata;

  if (m_Type == DATE) {
    m_Ordering = ORDERING_ORDERED;
    m_IsRegular = true;
    m_IsAveragable = false;
    m_HasZeropoint = false;
  } else {

    // get ordering
    string orderstring = m_Metadata.getProperty("ordering","");
      
    // numeric ordered attributes are averagable and zeropoint by default
    string def;
    if (m_Type == NUMERIC
	&& orderString.compareTo("modulo") != 0
	&& orderString.compareTo("symbolic") != 0)
      def = "true";
    else def = "false";
      
    // determine bool states
    m_IsAveragable =
      (m_Metadata.getProperty("averageable",def).compareTo("true") == 0);
    m_HasZeropoint =
      (m_Metadata.getProperty("zeropoint",def).compareTo("true") == 0);
    // averagable or zeropoint implies regular
    if (m_IsAveragable || m_HasZeropoint) def = "true";
    m_IsRegular =
      (m_Metadata.getProperty("regular",def).compareTo("true") == 0);
      
    // determine ordering
    if (orderString.compareTo("symbolic") == 0)
      m_Ordering = ORDERING_SYMBOLIC;
    else if (orderString.compareTo("ordered") == 0)
      m_Ordering = ORDERING_ORDERED;
    else if (orderString.compareTo("modulo") == 0)
      m_Ordering = ORDERING_MODULO;
    else {
      if (m_Type == NUMERIC || m_IsAveragable || m_HasZeropoint)
	m_Ordering = ORDERING_ORDERED;
      else m_Ordering = ORDERING_SYMBOLIC;
    }
  }

  // consistency checks
  if (m_IsAveragable && !m_IsRegular)
    throw IllegalArgumentException("An averagable attribute must be regular");
  if (m_HasZeropoint && !m_IsRegular)
    throw IllegalArgumentException("A zeropoint attribute must be regular");
  if (m_IsRegular && m_Ordering == ORDERING_SYMBOLIC)
    throw IllegalArgumentException("A symbolic attribute cannot be regular");
  if (m_IsAveragable && m_Ordering != ORDERING_ORDERED)
    throw IllegalArgumentException("An averagable attribute must be ordered");
  if (m_HasZeropoint && m_Ordering != ORDERING_ORDERED)
    throw IllegalArgumentException("A zeropoint attribute must be ordered");

  // determine weight
  m_Weight = 1.0;
  string weightstring = m_Metadata.getProperty("weight");
  if (weightstring != NULL) {
    try{
      m_Weight = Double.valueOf(weightString).doubleValue();
    } catch (NumberFormatException e) {
      // Check if value is really a number
      std::stringstream ss; 
      ss << "Not a valid attribute weight: '" << weightstring << "'"; 
      throw IllegalArgumentException(ss.str());
    }
  }

  // determine numeric range
  if (m_Type == NUMERIC) setNumericRange(m_Metadata.getProperty("range"));
}

void Attribute::setNumericRange(string rangeString) {
  // set defaults
  m_LowerBound = Double.NEGATIVE_INFINITY;
  m_LowerBoundIsOpen = false;
  m_UpperBound = Double.POSITIVE_INFINITY;
  m_UpperBoundIsOpen = false;

  if (rangestring == NULL) return;

  // set up a tokenzier to parse the string
  StreamTokenizer tokenizer =
    new StreamTokenizer(new StringReader(rangeString));
  tokenizer.resetSyntax();         
  tokenizer.whitespaceChars(0, ' ');    
  tokenizer.wordChars(' '+1,'\u00FF');
  tokenizer.ordinaryChar('[');
  tokenizer.ordinaryChar('(');
  tokenizer.ordinaryChar(',');
  tokenizer.ordinaryChar(']');
  tokenizer.ordinaryChar(')');

  std::stringstream ss; 
  try {

    // get opening brace
    tokenizer.nextToken();
    if (tokenizer.ttype == '[') m_LowerBoundIsOpen = false;
    else if (tokenizer.ttype == '(') m_LowerBoundIsOpen = true;
    else {
      ss.flush();
      ss << "Expected opening brace on range, found: " << tokenizer.toString(); 
      throw IllegalArgumentException(ss.str());
    }

    // get lower bound
    tokenizer.nextToken();
    if (tokenizer.ttype != tokenizer.TT_WORD) {
      ss.flush();
      ss << "Expected lower bound in range, found: " << tokenizer.toString();
      throw IllegalArgumentException(ss.str());
    }
    if (tokenizer.sval.compareToIgnoreCase("-inf") == 0)
      m_LowerBound = Double.NEGATIVE_INFINITY;
    else if (tokenizer.sval.compareToIgnoreCase("+inf") == 0)
      m_LowerBound = Double.POSITIVE_INFINITY;
    else if (tokenizer.sval.compareToIgnoreCase("inf") == 0)
      m_LowerBound = Double.NEGATIVE_INFINITY;
    else try {
	m_LowerBound = Double.valueOf(tokenizer.sval).doubleValue();
      } catch (NumberFormatException e) {
	ss.flush();
	ss << "Expected lower bound in range, found: '" << tokenizer.sval << "'"; 
	throw IllegalArgumentException(ss.str());
      }

    // get separating comma
    if (tokenizer.nextToken() != ',') {
      ss.flush();
      ss << "Expected comma in range, found: " << tokenizer.toString(); 
      throw IllegalArgumentException(ss.str());
    }
    // get upper bound
    tokenizer.nextToken();
    if (tokenizer.ttype != tokenizer.TT_WORD){
      ss.flush();
      ss << "Expected upper bound in range, found: " << tokenizer.toString();
      throw IllegalArgumentException(ss.str());
    }
    if (tokenizer.sval.compareToIgnoreCase("-inf") == 0)
      m_UpperBound = Double.NEGATIVE_INFINITY;
    else if (tokenizer.sval.compareToIgnoreCase("+inf") == 0)
      m_UpperBound = Double.POSITIVE_INFINITY;
    else if (tokenizer.sval.compareToIgnoreCase("inf") == 0)
      m_UpperBound = Double.POSITIVE_INFINITY;
    else try {
	m_UpperBound = Double.valueOf(tokenizer.sval).doubleValue();
      } catch (NumberFormatException e) {
	ss.flush();
	ss << "Expected upper bound in range, found: '" << tokenizer.sval << "'";
	throw IllegalArgumentException(ss.str());
      }

    // get closing brace
    tokenizer.nextToken();
    
    if (tokenizer.ttype == ']') m_UpperBoundIsOpen = false;
    else if (tokenizer.ttype == ')') m_UpperBoundIsOpen = true;
    else {
      ss.flush();
      ss << "Expected closing brace on range, found: " << tokenizer.toString();
      throw IllegalArgumentException(ss.str());
    }
    // check for rubbish on end
    if (tokenizer.nextToken() != tokenizer.TT_EOF){
      ss.flush();
      ss << "Expected end of range string, found: " << tokenizer.toString(); 
      throw IllegalArgumentException(ss.str());
    }
  } catch (IOException e) {
    ss.flush();
    ss << "IOException reading attribute range string: " << e.getMessage();
    throw IllegalArgumentException(ss.str());
  }

  if (m_UpperBound < m_LowerBound) {
    ss.flush();
    ss << "Upper bound (" << m_UpperBound 
       << ") on numeric range is" << " less than lower bound (" << m_LowerBound + ")!";
    throw IllegalArgumentException(ss.str());
  }
}

#ifdef _GEN_EXECUTABLE_
void main(int argc, char *argv[]) {

  try {
      
    // Create numeric attributes "length" and "weight"
    Attribute length = new Attribute("length");
    Attribute weight = new Attribute("weight");

    // Create date attribute "date"
    Attribute date = new Attribute("date", "yyyy-MM-dd HH:mm:ss");

    cout << date << endl;
    double dd = date.parseDate("2001-04-04 14:13:55");
    cout << "Test date = " << dd << endl;
    cout << date.formatDate(dd) << endl;

    dd = new Date().getTime();
    cout << "Date now = " << dd << endl;
    cout << date.formatDate(dd) << endl;
      
    // Create vector to hold nominal values "first", "second", "third" 
    FastVector my_nominal_values = new FastVector(3); 
    my_nominal_values.addElement("first"); 
    my_nominal_values.addElement("second"); 
    my_nominal_values.addElement("third"); 
      
    // Create nominal attribute "position" 
    Attribute position = new Attribute("position", my_nominal_values);

    // Print the name of "position"
    cout << "Name of \"position\": " << position.name() << endl;

    // Print the values of "position"
    Enumeration attValues = position.enumerateValues();
    while (attValues.hasMoreElements()) {
      string string = (String)attValues.nextElement();
      cout << "Value of \"position\": " << string << endl;
    }

    // Shallow copy attribute "position"
    Attribute copy = (Attribute) position.copy();

    // Test if attributes are the same
    cout << "Copy is the same as original: " << copy.equals(position) << endl;

    // Print index of attribute "weight" (should be unset: -1)
    cout << "Index of attribute \"weight\" (should be -1): " << 
      weight.index() << endl;

    // Print index of value "first" of attribute "position"
    cout << "Index of value \"first\" of \"position\" (should be 0): " <<
      position.indexOfValue("first") << endl;

    // Tests type of attribute "position"
    cout << "\"position\" is numeric: " << position.isNumeric() << endl;
    cout << "\"position\" is nominal: " << position.isNominal() << endl;
    cout << "\"position\" is string: " << position.isString() << endl;

    // Prints name of attribute "position"
    cout << "Name of \"position\": " << position.name() << endl;
    
    // Prints number of values of attribute "position"
    cout << "Number of values for \"position\": " 
	 << position.numValues() << endl;

    // Prints the values (againg)
    for (int i = 0; i < position.numValues(); i++) {
      cout << "Value " << i << ": " << position.value(i) << endl;
    }

    // Prints the attribute "position" in ARFF format
    cout << position << endl;

    // Checks type of attribute "position" using constants
    switch (position.type()) {
    case Attribute.NUMERIC:
      cout << "\"position\" is numeric" << endl;
      break;
    case Attribute.NOMINAL:
      cout << "\"position\" is nominal" << endl;
      break;
    case Attribute.STRING:
      cout << "\"position\" is string" << endl;
      break;
    case Attribute.DATE:
      cout << "\"position\" is date" << endl;
      break;
    case Attribute.RELATIONAL:
      cout << "\"position\" is relation-valued" << endl;
      break;
    default:
      cout << "\"position\" has unknown type" << endl;
    }

    FastVector atts = new FastVector(1);
    atts.addElement(position);
    Instances relation = new Instances("Test", atts, 0);
    Attribute relationValuedAtt = new Attribute("test", relation);
    cout << relationValuedAtt << endl;
  } catch (Exception e) {
    e.printStackTrace();
  }
}
#endif
  
