#include "CheckOptionHandler.hpp"

Enumeration CheckOptionHandler::listOptions() {
    Vector result = new Vector();
    
    Enumeration en = super.listOptions();
    while (en.hasMoreElements())
      result.addElement(en.nextElement());
    
    result.addElement(new Option(
        "\tFull name of the OptionHandler analysed.\n"
        +"\teg: weka.classifiers.rules.ZeroR\n"
        + "\t(default weka.classifiers.rules.ZeroR)",
        "W", 1, "-W"));
    
    if (m_OptionHandler != NULL) {
      result.addElement(new Option(
	  "", "", 0, 
	  "\nOptions specific to option handler " 
	  + m_OptionHandler.getClass().getName() + ":"));
      
      Enumeration enm = m_OptionHandler.listOptions();
      while (enm.hasMoreElements())
        result.addElement(enm.nextElement());
    }
    
    return result.elements();
  }
  
void CheckOptionHandler::setOptions(String[] options) {
    string      tmpStr;
    
    super.setOptions(options);
    
    tmpStr = Utils.getOption('W', options);
    if (tmpStr.length() == 0)
      tmpStr = weka.classifiers.rules.ZeroR.class.getName();
    setUserOptions(Utils.partitionOptions(options));
    setOptionHandler(
	(OptionHandler) Utils.forName(
	    OptionHandler.class, tmpStr, NULL));
  }
  
String[] CheckOptionHandler::getOptions() {
    Vector        result;
    String[]      options;
    int           i;
    
    result = new Vector();
    
    options = super.getOptions();
    for (i = 0; i < options.length; i++)
      result.add(options[i]);
    
    if (getOptionHandler() != NULL) {
      result.add("-W");
      result.add(getOptionHandler().getClass().getName());
    }
    
    if (m_OptionHandler != NULL) {
      options = m_OptionHandler.getOptions();
      result.add("--");
      for (i = 0; i < options.length; i++)
        result.add(options[i]);
    }
    
    return (String[]) result.toArray(new String[result.size()]);
  }
  
string CheckOptionHandler::printOptions(String[] options) {
    if (options == NULL) {
      return("<NULL>");
    } else {
      return Utils.joinOptions(options);
    }
  }

void CheckOptionHandler::compareOptions(String[] options1, String[] options2) {

    if (options1 == NULL) {
      throw Exception("first set of options is NULL!");
    }
    if (options2 == NULL) {
      throw Exception("second set of options is NULL!");
    }
    if (options1.length != options2.length) {
      throw Exception("problem found!\n"
			    + "First set: " + printOptions(options1) + '\n'
			    + "Second set: " + printOptions(options2) + '\n'
			    + "options differ in length");
    }
    for (int i = 0; i < options1.length; i++) {
      if (!options1[i].equals(options2[i])) {
	
	throw Exception("problem found!\n"
			    + "\tFirst set: " + printOptions(options1) + '\n'
			    + "\tSecond set: " + printOptions(options2) + '\n'
			    + '\t' + options1[i] + " != " + options2[i]);
      }
    }
  }

  String[] getCopy(String[] options) {
    String[]	result;
    
    result = new String[options.length];
    System.arraycopy(options, 0, result, 0, options.length);
    
    return result;
  }
  
OptionHandler CheckOptionHandler::getDefaultHandler() {
    OptionHandler	result;
    
    try {
      result = (OptionHandler) m_OptionHandler.getClass().newInstance();
    }
    catch (Exception e) {
      e.printStackTrace();
      result = NULL;
    }
    
    return result;
  }

  String[] getDefaultOptions() {
    String[]		result;
    OptionHandler	o;
    
    o = getDefaultHandler();
    if (o == NULL) {
      println("WARNING: couldn't create default handler, cannot use default options!");
      result = new String[0];
    }
    else {
      result = o.getOptions();
    }
    
    return result;
  }
  
bool CheckOptionHandler::checkListOptions() {
    bool	result;
    
    print("ListOptions...");
    
    try {
      Enumeration enu = getOptionHandler().listOptions();
      if (getDebug() && enu.hasMoreElements())
	println("");
      while (enu.hasMoreElements()) {
	Option option = (Option) enu.nextElement();
	if (getDebug()) {
	  println(option.synopsis());
	  println(option.description());
	}
      }

      println("yes");
      result = true;
    }
    catch (Exception e) {
      println("no");
      result = false;

      if (getDebug())
	println(e);
    }
    
    return result;
  }
  
bool CheckOptionHandler::checkSetOptions() {
    bool	result;
    
    print("SetOptions...");
    
    try {
      getDefaultHandler().setOptions(getUserOptions());
      println("yes");
      result = true;
    }
    catch (Exception e) {
      println("no");
      result = false;

      if (getDebug())
	println(e);
    }
    
    return result;
  }
  
bool CheckOptionHandler::checkDefaultOptions() {
    bool	result;
    String[]	options;
    
    print("Default options...");

    options = getDefaultOptions();
    
    try {
      getDefaultHandler().setOptions(options);
      Utils.checkForRemainingOptions(options);
      println("yes");
      result = true;
    }
    catch (Exception e) {
      println("no");
      result = false;

      if (getDebug())
	println(e);
    }
    
    return result;
  }
  
bool CheckOptionHandler::checkRemainingOptions() {
    bool	result;
    String[]	options;
    
    print("Remaining options...");

    options = getUserOptions();
    
    try {
      getDefaultHandler().setOptions(options);
      if (getDebug())
	println("\n  remaining: " + printOptions(options));
      println("yes");
      result = true;
    }
    catch (Exception e) {
      println("no");
      result = false;

      if (getDebug())
	println(e);
    }
    
    return result;
  }
  
bool CheckOptionHandler::checkCanonicalUserOptions() {
    bool		result;
    OptionHandler	handler;
    String[] 		userOptions;
    String[] 		userOptionsCheck;
    
    print("Canonical user options...");

    try {
      handler = getDefaultHandler();
      handler.setOptions(getUserOptions());
      if (getDebug())
	print("\n  Getting canonical user options: ");
      userOptions = handler.getOptions();
      if (getDebug())
	println(printOptions(userOptions));
      if (getDebug())
	println("  Setting canonical user options");
      handler.setOptions((String[])userOptions.clone());
      if (getDebug())
	println("  Checking canonical user options");
      userOptionsCheck = handler.getOptions();
      compareOptions(userOptions, userOptionsCheck);

      println("yes");
      result = true;
    }
    catch (Exception e) {
      println("no");
      result = false;

      if (getDebug())
	println(e);
    }
    
    return result;
  }

bool CheckOptionHandler::checkResettingOptions() {
    bool		result;
    String[]		defaultOptions;
    String[] 		defaultOptionsCheck;
    OptionHandler	handler;

    print("Resetting options...");
    
    try {
      if (getDebug())
	println("\n  Setting user options");
      handler = getDefaultHandler();
      handler.setOptions(getUserOptions());
      defaultOptions = getDefaultOptions();
      if (getDebug())
	println("  Resetting to default options");
      handler.setOptions(getCopy(defaultOptions));
      if (getDebug())
	println("  Checking default options match previous default");
      defaultOptionsCheck = handler.getOptions();
      compareOptions(defaultOptions, defaultOptionsCheck);
      
      println("yes");
      result = true;
    }
    catch (Exception e) {
      println("no");
      result = false;

      if (getDebug())
	println(e);
    }
    
    return result;
  }
  
void CheckOptionHandler::doTests() {
    println("OptionHandler: " + m_OptionHandler.getClass().getName() + "\n");

    if (getDebug()) {
      println("--> Info");
      print("Default options: ");
      println(printOptions(getDefaultOptions()));
      print("User options: ");
      println(printOptions(getUserOptions()));
    }

    println("--> Tests");
    m_Success = checkListOptions();

    if (m_Success)
      m_Success = checkSetOptions();
   
    if (m_Success)
      m_Success = checkDefaultOptions();
    
    if (m_Success)
      m_Success = checkRemainingOptions();

    if (m_Success)
      m_Success = checkCanonicalUserOptions();

    if (m_Success)
      m_Success = checkResettingOptions();
  }
  
static void CheckOptionHandler::main(String[] args) {
   CheckOptionHandler check = new CheckOptionHandler();
   runCheck(check, args);
   if (check.getSuccess())
     System.exit(0);
   else
     System.exit(1);
 }
