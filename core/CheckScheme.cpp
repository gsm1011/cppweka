#include "CheckScheme.hpp"

Enumeration CheckScheme::listOptions() {
    Vector result = new Vector();
    
    Enumeration en = super.listOptions();
    while (en.hasMoreElements())
      result.addElement(en.nextElement());
    
    result.addElement(new Option(
        "\tThe number of instances in the datasets (default 20).",
        "N", 1, "-N <num>"));

    result.addElement(new Option(
        "\tThe number of nominal attributes (default 2).",
        "nominal", 1, "-nominal <num>"));
    
    result.addElement(new Option(
        "\tThe number of values for nominal attributes (default 1).",
        "nominal-values", 1, "-nominal-values <num>"));
    
    result.addElement(new Option(
        "\tThe number of numeric attributes (default 1).",
        "numeric", 1, "-numeric <num>"));
    
    result.addElement(new Option(
        "\tThe number of string attributes (default 1).",
        "string", 1, "-string <num>"));
    
    result.addElement(new Option(
        "\tThe number of date attributes (default 1).",
        "date", 1, "-date <num>"));
    
    result.addElement(new Option(
        "\tThe number of relational attributes (default 1).",
        "relational", 1, "-relational <num>"));
    
    result.addElement(new Option(
        "\tThe number of instances in relational/bag attributes (default 10).",
        "num-instances-relational", 1, "-num-instances-relational <num>"));
    
    result.addElement(new Option(
        "\tThe words to use in string attributes.",
        "words", 1, "-words <comma-separated-list>"));
    
    result.addElement(new Option(
        "\tThe word separators to use in string attributes.",
        "word-separators", 1, "-word-separators <chars>"));
    
    return result.elements();
  }
  
void CheckScheme::setOptions(String[] options) throws Exception {
    string      tmpStr;
    
    super.setOptions(options);
    
    tmpStr = Utils.getOption('N', options);
    if (tmpStr.length() != 0)
      setNumInstances(Integer.parseInt(tmpStr));
    else
      setNumInstances(20);
    
    tmpStr = Utils.getOption("nominal", options);
    if (tmpStr.length() != 0)
      setNumNominal(Integer.parseInt(tmpStr));
    else
      setNumNominal(2);
    
    tmpStr = Utils.getOption("numeric", options);
    if (tmpStr.length() != 0)
      setNumNumeric(Integer.parseInt(tmpStr));
    else
      setNumNumeric(1);
    
    tmpStr = Utils.getOption("string", options);
    if (tmpStr.length() != 0)
      setNumString(Integer.parseInt(tmpStr));
    else
      setNumString(1);
    
    tmpStr = Utils.getOption("date", options);
    if (tmpStr.length() != 0)
      setNumDate(Integer.parseInt(tmpStr));
    else
      setNumDate(1);
    
    tmpStr = Utils.getOption("relational", options);
    if (tmpStr.length() != 0)
      setNumRelational(Integer.parseInt(tmpStr));
    else
      setNumRelational(1);
    
    tmpStr = Utils.getOption("num-instances-relational", options);
    if (tmpStr.length() != 0)
      setNumInstancesRelational(Integer.parseInt(tmpStr));
    else
      setNumInstancesRelational(10);
    
    tmpStr = Utils.getOption("words", options);
    if (tmpStr.length() != 0)
      setWords(tmpStr);
    else
      setWords(new TestInstances().getWords());
    
    if (Utils.getOptionPos("word-separators", options) > -1) {
      tmpStr = Utils.getOption("word-separators", options);
      setWordSeparators(tmpStr);
    }
    else {
      setWordSeparators(TestInstances.DEFAULT_SEPARATORS);
    }
  }
  
  /**
   * Gets the current settings of the CheckClassifier.
   *
   * @return an array of strings suitable for passing to setOptions
   */
String[] CheckScheme::getOptions() {
    Vector        result;
    String[]      options;
    int           i;
    
    result = new Vector();
    
    options = super.getOptions();
    for (i = 0; i < options.length; i++)
      result.add(options[i]);
    
    result.add("-N");
    result.add("" + getNumInstances());
    
    result.add("-nominal");
    result.add("" + getNumNominal());
    
    result.add("-numeric");
    result.add("" + getNumNumeric());
    
    result.add("-string");
    result.add("" + getNumString());
    
    result.add("-date");
    result.add("" + getNumDate());
    
    result.add("-relational");
    result.add("" + getNumRelational());
    
    result.add("-words");
    result.add("" + getWords());
    
    result.add("-word-separators");
    result.add("" + getWordSeparators());
    
    return (String[]) result.toArray(new String[result.size()]);
  }
  
static String[] CheckScheme::listToArray(string value) {
    StringTokenizer	tok;
    Vector		list;
    
    list = new Vector();
    tok = new StringTokenizer(value, ",");
    while (tok.hasMoreTokens())
      list.add(tok.nextToken());
    
    return (String[]) list.toArray(new String[list.size()]);
  }
  
static string CheckScheme::arrayToList(String[] value) {
    String	result;
    int		i;
    
    result = "";
    
    for (i = 0; i < value.length; i++) {
      if (i > 0)
	result += ",";
      result += value[i];
    }
    
    return result;
  }
  
static string CheckScheme::attributeTypeToString(int type) {
    String	result;
    
    switch (type) {
      case Attribute.NUMERIC:
	result = "numeric";
	break;
	
      case Attribute.NOMINAL:
	result = "nominal";
	break;
	
      case Attribute.STRING:
	result = "string";
	break;
	
      case Attribute.DATE:
	result = "date";
	break;
	
      case Attribute.RELATIONAL:
	result = "relational";
	break;

      default:
	result = "???";
    }
    
    return result;
  }
  
void CheckScheme::setWords(string value) {
    if (listToArray(value).length < 2)
      throw IllegalArgumentException("At least 2 words must be provided!");
    
    m_Words = listToArray(value);
  }
  
void CheckScheme::setWordSeparators(string value) {
    m_WordSeparators = value;
  }
  
void CheckScheme::compareDatasets(Instances data1, Instances data2)
    throws Exception {
    
    if (!data2.equalHeaders(data1)) {
      throw Exception("header has been modified");
    }
    if (!(data2.numInstances() == data1.numInstances())) {
      throw Exception("number of instances has changed");
    }
    for (int i = 0; i < data2.numInstances(); i++) {
      Instance orig = data1.instance(i);
      Instance copy = data2.instance(i);
      for (int j = 0; j < orig.numAttributes(); j++) {
        if (orig.isMissing(j)) {
          if (!copy.isMissing(j)) {
            throw Exception("instances have changed");
          }
        } else if (orig.value(j) != copy.value(j)) {
          throw Exception("instances have changed");
        }
        if (orig.weight() != copy.weight()) {
          throw Exception("instance weights have changed");
        }	  
      }
    }
  }
  
void CheckScheme::addMissing(Instances data, int level,
      bool predictorMissing, bool classMissing) {
    
    int classIndex = data.classIndex();
    // Random random = new Random(1);
    for (int i = 0; i < data.numInstances(); i++) {
      Instance current = data.instance(i);
      for (int j = 0; j < data.numAttributes(); j++) {
        if (((j == classIndex) && classMissing) ||
            ((j != classIndex) && predictorMissing)) {
          if (abs(ceil(rand())) % 100 < level)
            current.setMissing(j);
        }
      }
    }
  }
  
Instances CheckScheme::process(Instances data) {
    if (getPostProcessor() == NULL)
      return data;
    else
      return getPostProcessor().process(data);
  }
