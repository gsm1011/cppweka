for file in *.java; do mv $file `basename $file .java`.cpp; done
sed -i 's/private static final long serialVersionUID/\/\/ private static final long serialVersionUID/g' *.cpp
sed -i 's/public Serializable, /\/*public Serializable, *\//g' *.cpp
sed -i 's/^public class/class/g' *.cpp
sed -i 's/^import/\/\/ import/g' *.cpp
sed -i 's/^package/\/\/ package/g' *.cpp
sed -i 's/\.java/\.cpp/g' *.cpp
sed -i 's/boolean/bool/g' *.cpp
sed -i 's/throw new/throw/g' *.cpp
sed -i 's/Math\.//g' *.cpp
sed -i 's/String /string /g' *.cpp
sed -i 's/null/NULL/g' *.cpp
