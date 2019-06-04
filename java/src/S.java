public class S {

	public static String concat(String s1, String s2) {
		return s1 + s2;
	}

	public static Integer size(String s1) {
		return s1.length();
	}

    public static Integer count(String s1, String s2) {

        int val = 0;

        for (int i = 0; i < s1.length(); i++)
            val += String.valueOf(s1.charAt(i)).equals(s2) ? 1 : 0;

        return val;
    }

    public static String get(String s1, Integer i) {
        return String.valueOf(s1.charAt(i));
    }

    public static String substring(String s1, Integer min, Integer max) {
        return s1.substring(min, max);
    }

    public static Boolean equals(String s1, String s2) {
        return s1.equals(s2);
    }
}
