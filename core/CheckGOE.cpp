CheckGOE::CheckGOE() {
    super();
    
    // set default options
    try {
	setOptions(new String[0]);
    }
    catch (Exception e) {
	e.printStackTrace();
    }
}
  
Enumeration CheckGOE::listOptions() {
    Vector result = new Vector();
    
    Enumeration en = super.listOptions();
    while (en.hasMoreElements())
	result.addElement(en.nextElement());
    
    result.addElement(new Option(
				 "\tSkipped properties.\n"
				 + "\t(default: capabilities,options)",
				 "ignored", 1, "-ignored <comma-separated list of properties>"));
    
    result.addElement(new Option(
				 "\tFull name of the class analysed.\n"
				 +"\teg: weka.classifiers.rules.ZeroR\n"
				 + "\t(default weka.classifiers.rules.ZeroR)",
				 "W", 1, "-W"));
    
    return result.elements();
}
  
void CheckGOE::setOptions(String[] options) throws Exception {
    string      tmpStr;
    
    super.setOptions(options);
    
    tmpStr = Utils.getOption('W', options);
    if (tmpStr.length() == 0)
	tmpStr = weka.classifiers.rules.ZeroR.class.getName();
    setObject(Utils.forName(Object.class, tmpStr, NULL));
    
    tmpStr = Utils.getOption("ignored", options);
    if (tmpStr.length() == 0)
	tmpStr = "capabilities,options";
    setIgnoredProperties(tmpStr);
}
  
/**
 * Gets the current settings of the object.
 *
 * @return 		an array of strings suitable for passing to setOptions
 */
String[] CheckGOE::getOptions() {
    Vector        result;
    String[]      options;
    int           i;
    
    result = new Vector();
    
    options = super.getOptions();
    for (i = 0; i < options.length; i++)
	result.add(options[i]);

    result.add("-ignored");
    result.add(getIgnoredProperties());
    
    if (getObject() != NULL) {
	result.add("-W");
	result.add(getObject().getClass().getName());
    }
    
    return (String[]) result.toArray(new String[result.size()]);
}
  
void CheckGOE::setIgnoredProperties(string value) {
    String[] 	props;
    int		i;
    
    m_IgnoredProperties.clear();
    props = value.split(",");
    for (i = 0; i < props.length; i++)
	m_IgnoredProperties.add(props[i]);
}

string CheckGOE::getIgnoredProperties() {
    String		result;
    Vector<String>	list;
    Iterator		iter;
    int			i;
    
    list = new Vector<String>();
    iter = m_IgnoredProperties.iterator();
    while (iter.hasNext())
	list.add((String) iter.next());
    
    // sort
    if (list.size() > 1)
	Collections.sort(list);
    
    result = "";
    for (i = 0; i < list.size(); i++) {
	if (i > 0)
	    result += ",";
	result += list.get(i);
    }
     
    return result;
}
  
bool CheckGOE::checkGlobalInfo() {
    bool 	result;
    Class	cls;
    
    print("Global info...");
    
    result = true;
    cls    = getObject().getClass();
    
    // test for globalInfo method
    try {
	cls.getMethod("globalInfo", (Class[]) NULL);
    }
    catch (Exception e) {
	result = false;
    }

    if (result)
	println("yes");
    else
	println("no");

    return result;
}

bool CheckGOE::checkToolTips() {
    bool 			result;
    Class			cls;
    BeanInfo			info;
    PropertyDescriptor[]	desc;
    int				i;
    Vector<String>		missing;
    String			suffix;
    
    print("Tool tips...");
    
    result = true;
    suffix = "TipText";
    cls    = getObject().getClass();
    
    // get properties
    try {
	info = Introspector.getBeanInfo(cls, Object.class);
	desc = info.getPropertyDescriptors();
    }
    catch (Exception e) {
	e.printStackTrace();
	desc = NULL;
    }

    // test for TipText methods
    if (desc != NULL) {
	missing = new Vector<String>();
      
	for (i = 0; i < desc.length; i++) {
	    // skip property?
	    if (m_IgnoredProperties.contains(desc[i].getName()))
		continue;
	    if ((desc[i].getReadMethod() == NULL) || (desc[i].getWriteMethod() == NULL))
		continue;
	  
	    try {
		cls.getMethod(desc[i].getName() + suffix, (Class[]) NULL);
	    }
	    catch (Exception e) {
		result = false;
		missing.add(desc[i].getName() + suffix);
	    }
	}
      
	if (result)
	    println("yes");
	else
	    println("no (missing: " + missing + ")");

    }
    else {
	println("maybe");
    }
    
    return result;
}
  
void CheckGOE::doTests() {
    println("Object: " + m_Object.getClass().getName() + "\n");

    println("--> Tests");

    m_Success = checkGlobalInfo();

    if (m_Success)
	m_Success = checkToolTips();
}
  
static void CheckGOE::main(String[] args) {
    CheckGOE check = new CheckGOE();
    runCheck(check, args);
    if (check.getSuccess())
	System.exit(0);
    else
	System.exit(1);
}
