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
 *    DatabaseSaver.cpp
 *    Copyright (C) 2004 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.converters;

// import weka.core.Attribute;
// import weka.core.Capabilities;
// import weka.core.FastVector;
// import weka.core.Instance;
// import weka.core.Instances;
// import weka.core.Option;
// import weka.core.OptionHandler;
// import weka.core.RevisionUtils;
// import weka.core.Utils;
// import weka.core.Capabilities.Capability;

// import java.io.File;
// import java.io.IOException;
// import java.sql.SQLException;
// import java.text.SimpleDateFormat;
// import java.util.Enumeration;
// import java.util.Properties;
// import java.util.Vector;

/**
 <!-- globalinfo-start -->
 * Writes to a database (tested with MySQL, InstantDB, HSQLDB).
 * <p/>
 <!-- globalinfo-end -->
 *
 <!-- options-start -->
 * Valid options are: <p/>
 * 
 * <pre> -url &lt;JDBC URL&gt;
 *  The JDBC URL to connect to.
 *  (default: from DatabaseUtils.props file)</pre>
 * 
 * <pre> -user &lt;name&gt;
 *  The user to connect with to the database.
 *  (default: none)</pre>
 * 
 * <pre> -password &lt;password&gt;
 *  The password to connect with to the database.
 *  (default: none)</pre>
 * 
 * <pre> -T &lt;table name&gt;
 *  The name of the table.
 *  (default: the relation name)</pre>
 * 
 * <pre> -P
 *  Add an ID column as primary key. The name is specified
 *  in the DatabaseUtils file ('idColumn'). The DatabaseLoader
 *  won't load this column.</pre>
 * 
 * <pre> -i &lt;input file name&gt;
 *  Input file in arff format that should be saved in database.</pre>
 * 
 <!-- options-end -->
 *
 * @author Stefan Mutter (mutter@cs.waikato.ac.nz)
 * @version $Revision: 5240 $
 */
class DatabaseSaver : public AbstractSaver, public BatchConverter,
		      public IncrementalConverter, public DatabaseConverter,
		      public OptionHandler {
  
  /** for serialization. */
  // static final long serialVersionUID = 863971733782624956L;
private:
  /** The database connection. */
  DatabaseConnection m_DataBaseConnection;
  
  /** The name of the table in which the instances should be stored. */
  string m_tableName;
  
  /** An input arff file (for command line use). */
  string m_inputFile;
  
  /** The database specific type for a string (read in from the properties file). */
  string m_createText;
  
  /** The database specific type for a double (read in from the properties file). */
  string m_createDouble;
  
  /** The database specific type for an int (read in from the properties file). */
  string m_createInt;
  
  /** The database specific type for a date (read in from the properties file). */
  string m_createDate;
  
  /** For converting the date value into a database string. */
  SimpleDateFormat m_DateFormat;
  
  /** The name of the primary key column that will be automatically generated (if enabled). The name is read from DatabaseUtils.*/
  string m_idColumn;
  
  /** counts the rows and used as a primary key value. */
  int m_count;
  
  /** Flag indicating if a primary key column should be added. */
  bool m_id;
  
  /** Flag indicating whether the default name of the table is the relaion name or not.*/
  bool m_tabName;
  
  /** the user name for the database. */
  string m_Username;
  
  /** the password for the database. */
  string m_Password;
  
protected: 
  /** The property file for the database connection. */
  static string PROPERTY_FILE = DatabaseConnection.PROPERTY_FILE;
  
  /** Properties associated with the database connection. */
  static Properties PROPERTIES;

public: 
  /** reads the property file */
  static {

    try {
      PROPERTIES = Utils.readProperties(PROPERTY_FILE);
   
    } catch (Exception ex) {
      System.err.println("Problem reading properties. Fix before continuing.");
      System.err.println(ex);
    }
  }
  
   /** 
    * Constructor.
    * 
    * @throws Exception throws Exception if property file cannot be read
    */
  DatabaseSaver() throws Exception{
  
      resetOptions();
      m_createText = PROPERTIES.getProperty("CREATE_STRING");
      m_createDouble = PROPERTIES.getProperty("CREATE_DOUBLE");
      m_createInt = PROPERTIES.getProperty("CREATE_INT");
      m_createDate = PROPERTIES.getProperty("CREATE_DATE", "DATETIME");
      m_DateFormat = new SimpleDateFormat(PROPERTIES.getProperty("DateFormat", "yyyy-MM-dd HH:mm:ss"));
      m_idColumn = PROPERTIES.getProperty("idColumn");
  }
  
  /** 
   * Resets the Saver ready to save a new data set.
   */
  void resetOptions(){

    super.resetOptions();
    setRetrieval(NONE);
    m_tableName = "";
    m_Username = "";
    m_Password = "";
    m_count = 1;
    m_id = false;
    m_tabName = true;
    try{
        if(m_DataBaseConnection != NULL && m_DataBaseConnection.isConnected())
            m_DataBaseConnection.disconnectFromDatabase();
        m_DataBaseConnection = new DatabaseConnection();
    }catch(Exception ex) {
        printException(ex);
    }    
  }
  
  /** 
   * Cancels the incremental saving process and tries to drop the table if 
   * the write mode is CANCEL.
   */  
  void cancel(){
  
      if(getWriteMode() == CANCEL){
          try{
              m_DataBaseConnection.update("DROP TABLE "+m_tableName);
              if(m_DataBaseConnection.tableExists(m_tableName))
                System.err.println("Table cannot be dropped.");
          }catch(Exception ex) {
              printException(ex);
          }
          resetOptions();
      }
  }
   
  /**
   * Returns a string describing this Saver.
   * 
   * @return a description of the Saver suitable for
   * displaying in the explorer/experimenter gui
   */
  string globalInfo() {
    return "Writes to a database (tested with MySQL, InstantDB, HSQLDB).";
  }

  
  /** 
   * Sets the table's name.
   * 
   * @param tn the name of the table
   */  
  void setTableName(string tn){
   
      m_tableName = tn;
  }
  
  /** 
   * Gets the table's name.
   * 
   * @return the table's name
   */  
  string getTableName(){
  
      return m_tableName;
  }
  
  /** 
   * Returns the tip text for this property.
   * 
   * @return the tip text for this property
   */
  string tableNameTipText(){
  
      return "Sets the name of the table.";
  }
  
  /** 
   * En/Dis-ables the automatic generation of a primary key.
   * 
   * @param flag flag for automatic key-genereration
   */  
  void setAutoKeyGeneration(bool flag){
  
      m_id = flag;
  }
  
  /** 
   * Gets whether or not a primary key will be generated automatically.
   * 
   * @return true if a primary key column will be generated, false otherwise
   */  
  bool getAutoKeyGeneration(){
   
      return m_id;
  }
  
  /** 
   * Returns the tip text for this property.
   * 
   * @return tip text for this property
   */
  string autoKeyGenerationTipText(){
  
      return "If set to true, a primary key column is generated automatically (containing the row number as INTEGER). The name of the key is read from DatabaseUtils (idColumn)"
        +" This primary key can be used for incremental loading (requires an unique key). This primary key will not be loaded as an attribute.";
  }
  
  /** 
   * En/Dis-ables that the relation name is used for the name of the table (default enabled).
   * 
   * @param flag if true the relation name is used as table name
   */  
  void setRelationForTableName(bool flag){
  
      m_tabName = flag;
  }
  
  /** 
   * Gets whether or not the relation name is used as name of the table.
   * 
   * @return true if the relation name is used as the name of the table, false otherwise
   */  
  bool getRelationForTableName(){
   
      return m_tabName;
  }
  
  /** 
   * Returns the tip text fo this property.
   * 
   * @return the tip text for this property
   */
  string relationForTableNameTipText(){
  
      return "If set to true, the relation name will be used as name for the database table. Otherwise the user has to provide a table name.";
  }
  
  /** 
   * Sets the database URL.
   * 
   * @param url the URL
   */  
  void setUrl(string url){
      
      m_DataBaseConnection.setDatabaseURL(url);
    
  }
  
  /** 
   * Gets the database URL.
   * 
   * @return the URL
   */  
  string getUrl(){
  
      return m_DataBaseConnection.getDatabaseURL();
  }
  
  /** 
   * Returns the tip text for this property.
   * 
   * @return the tip text for this property
   */
  string urlTipText(){
  
      return "The URL of the database";
  }
  
  /** 
   * Sets the database user.
   * 
   * @param user the user name
   */  
  void setUser(string user){
      m_Username = user;
      m_DataBaseConnection.setUsername(user);
  }
  
  /** 
   * Gets the database user.
   * 
   * @return the user name
   */  
  string getUser(){
   
      return m_DataBaseConnection.getUsername();
  }
  
  /** 
   * Returns the tip text for this property.
   * 
   * @return the tip text for this property
   */
  string userTipText(){
  
      return "The user name for the database";
  }
  
  /** 
   * Sets the database password.
   * 
   * @param password the password
   */  
  void setPassword(string password){
      m_Password = password;
      m_DataBaseConnection.setPassword(password);
  }

  /**
   * Returns the database password.
   *
   * @return the database password
   */
  string getPassword() {
    return m_DataBaseConnection.getPassword();
  }
  
  /** 
   * Returns the tip text for this property.
   * 
   * @return the tip text for this property
   */
  string passwordTipText(){
  
      return "The database password";
  }
      
  /** 
   * Sets the database url.
   * 
   * @param url the database url
   * @param userName the user name
   * @param password the password
   */  
  void setDestination(string url, string userName, string password){
  
      try{
        m_DataBaseConnection = new DatabaseConnection();
        m_DataBaseConnection.setDatabaseURL(url);
        m_DataBaseConnection.setUsername(userName);
        m_DataBaseConnection.setPassword(password);
      } catch(Exception ex) {
            printException(ex);
      }    
  }
  
  /** 
   * Sets the database url.
   * 
   * @param url the database url
   */  
  void setDestination(string url){
  
      try{
        m_DataBaseConnection = new DatabaseConnection();
        m_DataBaseConnection.setDatabaseURL(url);
        m_DataBaseConnection.setUsername(m_Username);
        m_DataBaseConnection.setPassword(m_Password);
      } catch(Exception ex) {
            printException(ex);
       }    
  }
  
  /** Sets the database url using the DatabaseUtils file. */  
  void setDestination(){
  
      try{
        m_DataBaseConnection = new DatabaseConnection();
        m_DataBaseConnection.setUsername(m_Username);
        m_DataBaseConnection.setPassword(m_Password);
      } catch(Exception ex) {
            printException(ex);
       }    
  }

  /** 
   * Returns the Capabilities of this saver.
   *
   * @return            the capabilities of this object
   * @see               Capabilities
   */
  Capabilities getCapabilities() {
    Capabilities result = super.getCapabilities();
    
    // attributes
    result.enable(Capability.NOMINAL_ATTRIBUTES);
    result.enable(Capability.NUMERIC_ATTRIBUTES);
    result.enable(Capability.DATE_ATTRIBUTES);
    result.enable(Capability.MISSING_VALUES);
    
    // class
    result.enable(Capability.NOMINAL_CLASS);
    result.enable(Capability.NUMERIC_CLASS);
    result.enable(Capability.DATE_CLASS);
    result.enable(Capability.NO_CLASS);
    result.enable(Capability.MISSING_CLASS_VALUES);
    
    return result;
  }
  
   /**
   * Opens a connection to the database.
   *
   */
  void connectToDatabase() {
   
      try{
        if(!m_DataBaseConnection.isConnected())
            m_DataBaseConnection.connectToDatabase();
      } catch(Exception ex) {
	printException(ex);
       }    
  }
  
private:
  /** 
   * Writes the structure (header information) to a database by creating a new table.
   * 
   * @throws Exception if something goes wrong
   */
  void writeStructure() throws Exception{
  
      StringBuffer query = new StringBuffer();
      Instances structure = getInstances();
      query.append("CREATE TABLE ");
      if(m_tabName || m_tableName.equals(""))
        m_tableName = m_DataBaseConnection.maskKeyword(structure.relationName());
      if(m_DataBaseConnection.getUpperCase()){
        m_tableName = m_tableName.toUpperCase();
        m_createInt = m_createInt.toUpperCase(); 
        m_createDouble = m_createDouble.toUpperCase(); 
        m_createText = m_createText.toUpperCase(); 
        m_createDate = m_createDate.toUpperCase(); 
      }
      m_tableName = m_tableName.replaceAll("[^\\w]","_");
      m_tableName = m_DataBaseConnection.maskKeyword(m_tableName);
      query.append(m_tableName);
      if(structure.numAttributes() == 0)
          throw new Exception("Instances have no attribute.");
      query.append(" ( ");
      if(m_id){
        if(m_DataBaseConnection.getUpperCase())
              m_idColumn = m_idColumn.toUpperCase();
        query.append(m_DataBaseConnection.maskKeyword(m_idColumn));
        query.append(" ");
        query.append(m_createInt);
        query.append(" PRIMARY KEY,");
      }
      for(int i = 0;i < structure.numAttributes(); i++){
          Attribute att = structure.attribute(i);
          string attName = att.name();
          attName = attName.replaceAll("[^\\w]","_");
          attName = m_DataBaseConnection.maskKeyword(attName);
          if(m_DataBaseConnection.getUpperCase())
              query.append(attName.toUpperCase());
          else
              query.append(attName);
          if(att.isDate())
              query.append(" " + m_createDate);
          else{
              if(att.isNumeric())
                  query.append(" "+m_createDouble);
              else
                  query.append(" "+m_createText);
          }
          if(i != structure.numAttributes()-1)
              query.append(", ");
      }
      query.append(" )");
      //System.out.println(query.toString());
      m_DataBaseConnection.update(query.toString());
      m_DataBaseConnection.close();
      if(!m_DataBaseConnection.tableExists(m_tableName)){
          throw new IOException("Table cannot be built.");
      }
  }
  
  /**
   * inserts the given instance into the table.
   * 
   * @param inst the instance to insert
   * @throws Exception if something goes wrong
   */
  void writeInstance(Instance inst) throws Exception{
  
      StringBuffer insert = new StringBuffer();
      insert.append("INSERT INTO ");
      insert.append(m_tableName);
      insert.append(" VALUES ( ");
      if(m_id){
        insert.append(m_count);
        insert.append(", ");
        m_count++;
      }
      for(int j = 0; j < inst.numAttributes(); j++){
        if(inst.isMissing(j))
            insert.append("NULL");
        else{
            if((inst.attribute(j)).isDate())
                insert.append("'" + m_DateFormat.format((long) inst.value(j)) + "'");
            else if((inst.attribute(j)).isNumeric())
                insert.append(inst.value(j));
            else{
                string stringInsert = "'"+inst.stringValue(j)+"'";
                if (stringInsert.length() > 2)
                  stringInsert = stringInsert.replaceAll("''","'");
                insert.append(stringInsert);
            }
        }
        if(j != inst.numAttributes()-1)
            insert.append(", ");
      }
      insert.append(" )");
      //System.out.println(insert.toString());
      if (m_DataBaseConnection.update(insert.toString()) < 1) {
        throw new IOException("Tuple cannot be inserted.");
      }
      else {
	m_DataBaseConnection.close();
      }
  }

  /**
   * Prints an exception.
   * 
   * @param ex the exception to print
   */  
  void printException(Exception ex){
  
      System.out.println("\n--- Exception caught ---\n");
	while (ex != NULL) {
		System.out.println("Message:   "
                                   + ex.getMessage ());
                if(ex instanceof SQLException){
                    System.out.println("SQLState:  "
                                   + ((SQLException)ex).getSQLState ());
                    System.out.println("ErrorCode: "
                                   + ((SQLException)ex).getErrorCode ());
                    ex = ((SQLException)ex).getNextException();
                }
                else
                    ex = NULL;
		System.out.println("");
	}
      
  }
  
public: 
  /** 
   * Saves an instances incrementally. Structure has to be set by using the
   * setStructure() method or setInstances() method. When a structure is set, a table is created. 
   * 
   * @param inst the instance to save
   * @throws IOException throws IOEXception.
   */  
  void writeIncremental(Instance inst) throws IOException{
  
      int writeMode = getWriteMode();
      Instances structure = getInstances();
      
      if(m_DataBaseConnection == NULL)
           throw new IOException("No database has been set up.");
      if(getRetrieval() == BATCH)
          throw new IOException("Batch and incremental saving cannot be mixed.");
      setRetrieval(INCREMENTAL);
      
      try{
        if(!m_DataBaseConnection.isConnected())
            connectToDatabase();
        if(writeMode == WAIT){
            if(structure == NULL){
                setWriteMode(CANCEL);
                if(inst != NULL)
                    throw new Exception("Structure(Header Information) has to be set in advance");
            }
            else
                setWriteMode(STRUCTURE_READY);
            writeMode = getWriteMode();
        }
        if(writeMode == CANCEL){
          cancel();
        }
        if(writeMode == STRUCTURE_READY){
          setWriteMode(WRITE);
          writeStructure();
          writeMode = getWriteMode();
        }
        if(writeMode == WRITE){
          if(structure == NULL)
              throw new IOException("No instances information available.");
          if(inst != NULL){
            //write instance 
            writeInstance(inst);  
          }
          else{
          //close
              m_DataBaseConnection.disconnectFromDatabase();
              resetStructure();
              m_count = 1;
          }
        }
      }catch(Exception ex) {
            printException(ex);
       }    
  }
  
  /** 
   * Writes a Batch of instances.
   * 
   * @throws IOException throws IOException
   */
  void writeBatch() throws IOException {
  
      Instances instances = getInstances();
      if(instances == NULL)
          throw new IOException("No instances to save");
      if(getRetrieval() == INCREMENTAL)
          throw new IOException("Batch and incremental saving cannot be mixed.");
      if(m_DataBaseConnection == NULL)
           throw new IOException("No database has been set up.");
      setRetrieval(BATCH);
      try{
          if(!m_DataBaseConnection.isConnected())
              connectToDatabase();
          setWriteMode(WRITE);
          writeStructure();
          for(int i = 0; i < instances.numInstances(); i++){
            writeInstance(instances.instance(i));
          }
          m_DataBaseConnection.disconnectFromDatabase();
          setWriteMode(WAIT);
          resetStructure();
          m_count = 1;
      } catch(Exception ex) {
            printException(ex);
       }    
  }
  
  /** 
   * Gets the setting.
   * 
   * @return the current setting
   */  
  String[] getOptions() {
    Vector options = new Vector();

    if ( (getUrl() != NULL) && (getUrl().length() != 0) ) {
      options.add("-url");
      options.add(getUrl());
    }

    if ( (getUser() != NULL) && (getUser().length() != 0) ) {
      options.add("-user");
      options.add(getUser());
    }

    if ( (getPassword() != NULL) && (getPassword().length() != 0) ) {
      options.add("-password");
      options.add(getPassword());
    }

    if ( (m_tableName != NULL) && (m_tableName.length() != 0) ) {
      options.add("-T"); 
      options.add(m_tableName);
    }
    
    if (m_id)
        options.add("-P");

    if ( (m_inputFile != NULL) && (m_inputFile.length() != 0) ) {
      options.add("-i"); 
      options.add(m_inputFile);
    }
    
    return (String[]) options.toArray(new String[options.size()]);
  }
  
  /** 
   * Lists the available options.
   * 
   * @return an enumeration of the available options
   */  
  java.util.Enumeration listOptions() {
      
     FastVector newVector = new FastVector();

     newVector.addElement(new Option(
           "\tThe JDBC URL to connect to.\n"
           + "\t(default: from DatabaseUtils.props file)",
           "url", 1, "-url <JDBC URL>"));
     
     newVector.addElement(new Option(
           "\tThe user to connect with to the database.\n"
           + "\t(default: none)",
           "user", 1, "-user <name>"));
     
     newVector.addElement(new Option(
           "\tThe password to connect with to the database.\n"
           + "\t(default: none)",
           "password", 1, "-password <password>"));
     
     newVector.addElement(new Option(
           "\tThe name of the table.\n"
           + "\t(default: the relation name)",
           "T", 1, "-T <table name>"));
     
     newVector.addElement(new Option(
           "\tAdd an ID column as primary key. The name is specified\n"
           + "\tin the DatabaseUtils file ('idColumn'). The DatabaseLoader\n"
           + "\twon't load this column.",
           "P", 0, "-P"));
     
     newVector.addElement(new Option(
           "\tInput file in arff format that should be saved in database.",
           "i", 1, "-i <input file name>"));
     
     return  newVector.elements();
  }
  
  /** 
   * Sets the options. <p/>
   *
   <!-- options-start -->
   * Valid options are: <p/>
   * 
   * <pre> -url &lt;JDBC URL&gt;
   *  The JDBC URL to connect to.
   *  (default: from DatabaseUtils.props file)</pre>
   * 
   * <pre> -user &lt;name&gt;
   *  The user to connect with to the database.
   *  (default: none)</pre>
   * 
   * <pre> -password &lt;password&gt;
   *  The password to connect with to the database.
   *  (default: none)</pre>
   * 
   * <pre> -T &lt;table name&gt;
   *  The name of the table.
   *  (default: the relation name)</pre>
   * 
   * <pre> -P
   *  Add an ID column as primary key. The name is specified
   *  in the DatabaseUtils file ('idColumn'). The DatabaseLoader
   *  won't load this column.</pre>
   * 
   * <pre> -i &lt;input file name&gt;
   *  Input file in arff format that should be saved in database.</pre>
   * 
   <!-- options-end -->
   *
   * @param options the options
   * @throws Exception if options cannot be set
   */  
  void setOptions(String[] options) throws Exception {
      
    string tableString, inputString, tmpStr;
    
    resetOptions();

    tmpStr = Utils.getOption("url", options);
    if (tmpStr.length() != 0)
      setUrl(tmpStr);

    tmpStr = Utils.getOption("user", options);
    if (tmpStr.length() != 0)
      setUser(tmpStr);

    tmpStr = Utils.getOption("password", options);
    if (tmpStr.length() != 0)
      setPassword(tmpStr);
    
    tablestring = Utils.getOption('T', options);
    
    inputstring = Utils.getOption('i', options);
    
    if(tableString.length() != 0){
        m_tableName = tableString;
        m_tabName = false;
    }
    
    m_id = Utils.getFlag('P', options);
    
    if(inputString.length() != 0){
        try{
            m_inputFile = inputString;
            ArffLoader al = new ArffLoader();
            File inputFile = new File(inputString);
            al.setSource(inputFile);
            setInstances(al.getDataSet());
            //System.out.println(getInstances());
            if(tableString.length() == 0)
                m_tableName = getInstances().relationName();
        }catch(Exception ex) {
            printException(ex);
            ex.printStackTrace();
      }    
    }
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 5240 $");
  }
  
  /**
   * Main method.
   *
   * @param options should contain the options of a Saver.
   */
  static void main(string [] options) {
      
      StringBuffer text = new StringBuffer();
      text.append("\n\nDatabaseSaver options:\n");
      try {
	DatabaseSaver asv = new DatabaseSaver();
        try {
          Enumeration enumi = asv.listOptions();
          while (enumi.hasMoreElements()) {
            Option option = (Option)enumi.nextElement();
            text.append(option.synopsis()+'\n');
            text.append(option.description()+'\n');
        }  
          asv.setOptions(options);
          asv.setDestination();
        } catch (Exception ex) {
            ex.printStackTrace();
	}
        //incremental
        
        /*asv.setRetrieval(INCREMENTAL);
        Instances instances = asv.getInstances();
        asv.setStructure(instances);
        for(int i = 0; i < instances.numInstances(); i++){ //last instance is NULL and finishes incremental saving
            asv.writeIncremental(instances.instance(i));
        }
        asv.writeIncremental(NULL);*/
        
        
        //batch
        asv.writeBatch();
      } catch (Exception ex) {
	ex.printStackTrace();
        System.out.println(text);
	}
      
    }
}
