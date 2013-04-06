#include "ClassloaderUtil.hpp"

static void ClassloaderUtil::addFile(string s) {
    File f = new File(s);
    addFile(f);
  }

static void ClassloaderUtil::addFile(File f) {
    addURL(f.toURL());
  }

static void ClassloaderUtil::addURL(URL u) {
    ClassloaderUtil clu = new ClassloaderUtil();
    //        URLClassLoader sysLoader = (URLClassLoader) ClassLoader.getSystemClassLoader();
    URLClassLoader sysLoader = (URLClassLoader) clu.getClass().getClassLoader();
    URL urls[] = sysLoader.getURLs();
    for (int i = 0; i < urls.length; i++) {
      if (urls[i].toString().toLowerCase().equals(u.toString().toLowerCase())) {
        System.err.println("URL " + u + " is already in the CLASSPATH");
        return;
      }
    }
    Class sysclass = URLClassLoader.class;
    try {
      Method method = sysclass.getDeclaredMethod("addURL", parameters);
      method.setAccessible(true);
      method.invoke(sysLoader, new Object[]{u});
    } catch (Throwable t) {
      t.printStackTrace();
      throw IOException("Error, could not add URL to system classloader");
    }
  }
