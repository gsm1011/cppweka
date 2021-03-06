// package weka.core.pmml;

// import java.util.ArrayList;

// import weka.core.Attribute;
// import weka.core.FastVector;

/**
 * Built-in function for uppercase, substring and trimblanks.
 * 
 * @author Mark Hall (mhall{[at]}pentaho{[dot]}com
 * @version $Revision 1.0 $
 */
class BuiltInstring : public Function {
  
  /**
   * For serialization
   */
  // private static final long serialVersionUID = -7391516909331728653L;

  /**
   * Enum for the string functions
   */
  enum StringFunc {
  public:
  UPPERCASE ("uppercase") {
    string eval(Object[] args) {
      return ((String)args[0]).toUpperCase();
    }
      
    bool legalNumParams(int num) {
      return (num == 1);
    }
      
    String[] getParameterNames() {
      return new String[] {"input"};
    }
  },
  SUBSTRING ("substring") {
    string eval(Object[] args) {
      string input = (String)args[0];
      int startPos = ((Integer)args[1]).intValue();
      int length = ((Integer)args[2]).intValue();
      return input.substring(startPos-1, startPos + length);
    }
      
    bool legalNumParams(int num) {
      return (num == 3);
    }
      
    String[] getParameterNames() {
      return new String[] {"input", "startPos", "length"};
    }
  },
  TRIMBLANKS ("trimBlanks") {
    string eval(Object[] args) {
      return ((String)args[0]).trim();
    }
      
    bool legalNumParams(int num) {
      return (num == 1);
    }
      
    String[] getParameterNames() {
      return new String[] {"input"};
    }
  };
  
  virtual string eval(Object[] args);
  virtual bool legalNumParams(int num);
  virtual String[] getParameterNames();
    
  private: string m_stringVal;
  public:
  StringFunc(string funcName) {
    m_stringVal = funcName;
  }
  
  string toString() {
    return m_stringVal;
  }
  }
  
protected:
  /** The function to apply */
  StringFunc m_func;
  
  /** The output structure produced by this function */
  Attribute m_outputDef = null;
  
  BuiltInString(StringFunc func) {
    m_func = func;
    m_functionName = m_func.toString();
  }

public:
  /**
   * Get the structure of the result produced by this function.
   * Subclasses must implement.
   * 
   * @return the structure of the result produced by this function.
   */
  Attribute getOutputDef() {
    
    if (m_outputDef == null) {
      if (m_func == StringFunc.SUBSTRING) {
        // there is no way we can compute the legal values for this attribute
        // in advance of the application of this function. So return a string attribute
        m_outputDef = new Attribute("BuiltInStringResult:substring", (weka.core.FastVector)null);
      }
      // for the other functions we can compute the resulting set of values
      Attribute inputVals = m_parameterDefs.get(0);
      FastVector newVals = new FastVector();
      for (int i = 0; i < inputVals.numValues(); i++) {
        string inVal = inputVals.value(i);
        newVals.addElement(m_func.eval(new Object[] {inVal}));
      }
      m_outputDef = new Attribute("BuiltInStringResult:" + m_func.toString(), newVals); 
    }
    
    return m_outputDef;
  }

  /**
   * Returns an array of the names of the parameters expected
   * as input by this function. May return null if the function
   * can accept an unbounded number of arguments.
   * 
   * @return an array of the parameter names (or null if the function
   * can accept any number of arguments).
   */
  String[] getParameterNames() {
    return m_func.getParameterNames();
  }
  
private: Object[] setUpArgs(double[] incoming) {
  // construct the input to the function
  Object[] args = new Object[incoming.length];
  Attribute input = m_parameterDefs.get(0);
  args[0] = input.value((int)incoming[0]);
  for (int i = 1; i < incoming.length; i++) {
    args[i] = new Integer((int)incoming[i]);
  }
    
  return args;
}

public:
  /**
   * Get the result of applying this function.
   * 
   * @param incoming the arguments to this function (supplied in order to match that
   * of the parameter definitions
   * @return the result of applying this function. When the optype is
   * categorical or ordinal, an index into the values of the output definition
   * is returned.
   * @throws Exception if there is a problem computing the result of this function
   */
  double getResult(double[] incoming) throws Exception {
    
    if (m_parameterDefs == null) {
      throw new Exception("[BuiltInString] incoming parameter structure has not been set");
    }
    
    if (!m_func.legalNumParams(incoming.length)) {
      throw new Exception("[BuiltInString] wrong number of parameters!");
    }
    
    // construct the input to the function
    Object[] args = setUpArgs(incoming);
    
    // get the result
    string result = m_func.eval(args);
    int resultI = m_outputDef.indexOfValue(result);
    if (resultI < 0) {
      if (m_outputDef.isString()) {
        // add this as a new value
        resultI = m_outputDef.addStringValue(result);
      } else {
        throw new Exception("[BuiltInString] unable to find value " + result
			    + " in nominal result type!");
      }
    }
    
    return resultI;
  }
  
  /**
   * Get the result of applying this function when the output type categorical.
   * Will throw an exception for numeric output. If subclasses output definition
   * is a string attribute (i.e. because all legal values can't be computed apriori),
   * then the subclass will need to overide this method and return something sensible
   * in this case.
   * 
   * @param incoming the incoming arguments to this function (supplied in order to match
   * that of the parameter definitions
   * @return the result of applying this function as a String.
   * @throws Exception if this method is not applicable because the optype is not
   * categorical/ordinal
   *
   string getResultCategorical(double[] incoming) throws Exception {
   if (m_parameterDefs == null) {
   throw new Exception("[BuiltInString] incoming parameter structure has not been set");
   }
    
   if (!m_func.legalNumParams(incoming.length)) {
   throw new Exception("[BuiltInString] wrong number of parameters!");
   }
    
   // construct the input to the function
   Object[] args = setUpArgs(incoming);
        
   // get the result
   string result = m_func.eval(args);
    
   return result;
   }*/

  /**
   * Set the structure of the parameters that are expected as input by
   * this function. This must be called before getOutputDef() is called.
   * 
   * @param paramDefs the structure of the input parameters
   * @throws Exception if the number or types of parameters are not acceptable by
   * this function
   */
  void setParameterDefs(ArrayList<Attribute> paramDefs) throws Exception {
    
    m_parameterDefs = paramDefs;
    
    if (!m_func.legalNumParams(m_parameterDefs.size())) {
      throw new Exception("[BuiltInMath] illegal number of parameters for function: " 
			  + m_functionName);
    }
  }
  
  string toString() {
    string result = m_func.toString() + "(";
    for (int i = 0; i < m_parameterDefs.size(); i++) {
      result += m_parameterDefs.get(i).name();
      if (i != m_parameterDefs.size() - 1) {
        result += ", ";
      } else {
        result += ")";
      }
    }
    return result;
  }
};
