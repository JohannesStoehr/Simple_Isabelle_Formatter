import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Main {

    private static final int INDENTION_SIZE = 2;
    private static final int MAX_NEW_LINES = 2;
    private static final int LINES_BEFORE_LEMMA_OR_SECTION = 2;
    private static final int MAX_LINE_LENGTH = 100;
    private static final String[] COMMENT_STARTERS = {"text"};
    private static final String[] TEXT_STARTERS = {"section", "subsection", "subsubsection"};
    private static final String[] LEMMA_STARTERS = {"lemma", "theorem"};
    private static final String[] OTHER_STARTERS = {"fun", "definition", "function", "datatype", "type_synonym", "theory", "begin", "sledgehammer_params", "abbreviation",
            "inductive", "locale", "end"};
    private static final String[] STEP_STARTERS = {"then", "have", "also", "finally", "hence", "thus", "moreover", "case", "show", "obtain"};
    private static final String STEP_STARTERS_REGEX = String.join("|", STEP_STARTERS);
    private static final String[] PROOF_HELPERS = {"using", "unfolding"};
    private static final String[] OPERATORS = {"\\+", "\\-", "\\*", "div", "=", "::", "`", "@", "#", "\\|", "\\\\<[a-zA-Z]*>"};
    private static final String OPERATOR_REGEX = "(" + String.join("|", OPERATORS) + ")";
    private static final String[] PROOVERS = {"verit", "full_types"};
    private static final String PROOVERS_REGEX = "(?!" + String.join("\\b)(?!", PROOVERS) + "\\b)";
    private static final String[] LINE_ENDERS = {"of", "where", "\\|"};
    private static final String[] LINE_STARTERS = {"then", "else"};
    private static final String[] OPENING_BRACKETS = {"\\(", "\\{", "\\\\<lbrakk>"};
    private static final String[] CLOSING_BRACKETS = {"\\)", "\\}", "\\\\<rbrakk>"};

    public static void main(String[] args) throws IOException {
        try (Stream<Path> paths = Files.walk(Path.of("."))) {
            paths.filter(Files::isRegularFile)
                    .filter(p -> !p.toString().contains("Clean"))
                    .filter(path -> path.toString().endsWith(".thy"))
                    .forEach(Main::processFile);
        }
    }

    private static void processFile(Path path) {
        File cleanFile = createCleanFile(path);

        List<String> lines;
        List<String> cleanLines = new ArrayList<>();
        try {
            lines = new ArrayList<>(Files.readAllLines(path));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        int newLines = 2;
        boolean insideQuotes = false;

        for (int i = 0; i < lines.size(); i++) {
            String line = lines.get(i).trim();
            line = line.replaceAll("\\s{2,}", " ");

            if (newLines >= MAX_NEW_LINES && line.isBlank()) {
                continue;
            } else if (line.isBlank()) {
                if (newLines < MAX_NEW_LINES) {
                    cleanLines.add("");
                }
                newLines++;
                continue;
            } else {
                newLines = 0;
            }

            newLines = addEmptyLinesBeforeLemmaOrSection(line, cleanLines, newLines);

            if (Stream.concat(Arrays.stream(TEXT_STARTERS), Arrays.stream(COMMENT_STARTERS)).anyMatch(line::startsWith)) {
                cleanLines.add(line);
                continue;
            }

            line = normalizeSpaces(line, insideQuotes);
            line = moveLineBreakers(line, cleanLines, lines, i);
            line = breakLine(line, lines, i + 1);
            line = removeMultipleProofHelpers(line, cleanLines);
            line = removeUnnecessaryBrackets(line);
            line = addAnds(line, lines, i + 1, cleanLines);
            line = breakLongLines(line, lines, i + 1);
            line = addApplyAutoBonk(line);

            if (line.isBlank()) {
                continue;
            }

            long numberOfQuotesInLine = line.chars().filter(ch -> ch == '"').count();
            if (numberOfQuotesInLine % 2 == 1) {
                insideQuotes = !insideQuotes;
            }

            if (shouldUniteWithLastLine(line, cleanLines)) {
                cleanLines.set(cleanLines.size() - 1, cleanLines.getLast() + " " + line);
            } else {
                cleanLines.add(line);
            }
        }

        indentLines(cleanLines);

        try {
            Files.write(cleanFile.toPath(), cleanLines);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static File createCleanFile(Path path) {
        String cleanFileName = path.toString().replace(".thy", "Clean.thy");
        File cleanFile = new File(cleanFileName);
        if (cleanFile.exists()) {
            if (!cleanFile.delete()) {
                throw new RuntimeException("Could not delete existing clean file: " + cleanFileName);
            }
        }
        try {
            if (!cleanFile.createNewFile()) {
                throw new RuntimeException("Could not create clean file: " + cleanFileName);
            }
        } catch (IOException e) {
            throw new RuntimeException("Could not create clean file: " + cleanFileName, e);
        }
        return cleanFile;
    }

    private static int addEmptyLinesBeforeLemmaOrSection(String line, List<String> cleanLines, int newLinesBefore) {
        if (Stream.concat(Arrays.stream(TEXT_STARTERS), Arrays.stream(LEMMA_STARTERS)).anyMatch(line::startsWith)) {
            int blankLinesToAdd = LINES_BEFORE_LEMMA_OR_SECTION;
            for (int i = cleanLines.size() - 1; i >= 0 && i >= cleanLines.size() - LINES_BEFORE_LEMMA_OR_SECTION; i--) {
                if (cleanLines.get(i).isBlank()) {
                    blankLinesToAdd--;
                } else {
                    break;
                }
            }
            for (int i = 0; i < blankLinesToAdd; i++) {
                cleanLines.add("");
            }
            return LINES_BEFORE_LEMMA_OR_SECTION;
        } else {
            return newLinesBefore;
        }
    }

    private static String normalizeSpaces(String line, boolean insideQuotes) {
        line = normalizeQuotationSpaces(line, insideQuotes);

        line = line.replaceAll("(?<![\\s_\"])" + OPERATOR_REGEX, " $0");
        line = line.replaceAll(OPERATOR_REGEX + "(?![\\s_\"])", "$0 ");

        line = line.replaceAll("(?<![\\\\\\s\"])<", " <");
        line = line.replaceAll("(?<!\\\\)<(?![\\s\"])", "< ");
        // TODO: FIX >

        for (String openingBracket : OPENING_BRACKETS) {
            line = line.replaceAll("(?<![({\\s\"]|^) " + openingBracket + "(?![0-9]+\\))", " " + openingBracket);
            line = line.replaceAll(openingBracket + "\\s", openingBracket);
        }
        for (String closingBracket : CLOSING_BRACKETS) {
            line = line.replaceAll(closingBracket + "(?![)}\\s\"])", closingBracket + " ");
            line = line.replaceAll("\\s" + closingBracket, closingBracket);
        }

        line = line.replaceAll("\\s,\\s|\\s,|,\\s", ",");
        line = line.replaceAll("\\s\\.\\s|\\s\\.", ". ");
        line = line.replaceAll("\\s;\\s|\\s;", "; ");

        line = line.replaceAll("\\s:\\s|\\s:(?!:)|:(?![\\s:])", ": ");

        line = line.replaceAll("\\[\\s", "[");
        line = line.replaceAll("(?<![({\\s\"]|^)\\[(?!of|OF)", " [");
        line = line.replaceAll("\\s\\[of\\s|\\s\\[of", "[of");
        line = line.replaceAll("\\s\\[OF\\s|\\s\\[OF", "[OF");
        line = line.replaceAll("\\s]", "]");
        line = line.replaceAll("](?![)}\\s\",])", "] ");

        line = line.replaceAll("(?<=(" + STEP_STARTERS_REGEX + "))(?=\")", " ");

        return line.trim();
    }

    private static String normalizeQuotationSpaces(String line, boolean insideQuotes) {
        String[] parts = line.split("\"", -1);

        if (parts.length == 1) {
            return line;
        } else if (parts[0].isEmpty()) {
            line = "\"";
        } else if (insideQuotes) {
            line = parts[0].trim() + "\"";
        } else {
            line = parts[0].trim() + " \"";
        }

        insideQuotes = !insideQuotes;

        StringBuilder lineBuilder = new StringBuilder(line);
        for (int i = 1; i < parts.length; i++) {
            if (insideQuotes) {
                lineBuilder.append(parts[i].trim());
            } else {
                lineBuilder.append(" ");
                if (!parts[i].isBlank()) {
                    lineBuilder.append(parts[i].trim());
                }
            }
            insideQuotes = !insideQuotes;

            if (i < parts.length - 1) {
                lineBuilder.append("\"");
            }
        }
        return lineBuilder.toString();
    }

    private static String moveLineBreakers(String line, List<String> cleanLines, List<String> lines, int currentIndex) {
        for (String lineEnder : LINE_ENDERS) {
            if (line.matches(lineEnder + "([\\s()\"].*)?")) {
                String lineEnderWithoutBackslash = lineEnder.replace("\\", "");
                cleanLines.set(cleanLines.size() - 1, cleanLines.getLast() + " " + lineEnderWithoutBackslash);
                line = line.substring(lineEnderWithoutBackslash.length()).trim();
            }
        }

        for (String lineStarter : LINE_STARTERS) {
            if (line.endsWith(lineStarter)) {
                lines.set(currentIndex + 1, lineStarter + " " + lines.get(currentIndex + 1));
                line = line.substring(0, line.length() - lineStarter.length()).trim();
            }
        }

        if (line.startsWith("and")) {
            cleanLines.set(cleanLines.size() - 1, cleanLines.getLast() + " and");
            return line.substring("and".length()).trim();
        } else if (line.startsWith("\"") && cleanLines.getLast().endsWith("\"")) {
            cleanLines.set(cleanLines.size() - 1, cleanLines.getLast() + " and");
            return line;
        } else {
            return line;
        }
    }

    private static String breakLine(String line, List<String> lines, int indexToAdd) {
        for (String lineEnder : LINE_ENDERS) {
            if (line.matches(".*[\\s)]" + lineEnder + "[\\s()].*")) {
                String[] parts = line.split(lineEnder, 2);
                if (parts.length == 2) {
                    lines.add(indexToAdd, parts[1].trim());
                }
                line = parts[0].trim() + " " + lineEnder.replace("\\", "");
            }
        }

        for (String lineStarter : LINE_STARTERS) {
            if (line.matches(".*[\\s)]" + lineStarter + "[\\s()].*")) {
                String[] parts = line.split(lineStarter, 3);
                if (parts[0].isBlank()) {
                    if (parts.length == 3) {
                        lines.add(indexToAdd, lineStarter + " " + parts[2].trim());
                    }
                    line = lineStarter + " " + parts[1].trim();
                } else {
                    if (parts.length == 2) {
                        lines.add(indexToAdd, lineStarter + " " + parts[1].trim());
                    } else if (parts.length == 3) {
                        lines.add(indexToAdd, lineStarter + " " + parts[1].trim());
                        lines.add(indexToAdd + 1, lineStarter + " " + parts[2].trim());
                    }
                    line = parts[0].trim();
                }
            }
        }

        if (line.contains("apply") && (Arrays.stream(PROOF_HELPERS).anyMatch(line::startsWith) || line.indexOf("apply") < Arrays.stream(PROOF_HELPERS).mapToInt(line::indexOf).min().orElse(-1))) {
            String[] parts = line.split("apply ", 2);

            String[] afterApply;
            StringBuilder proveMethod;
            String remainder;

            if (parts[1].trim().startsWith("(")) {
                afterApply = parts[1].split("\\)", -1);

                proveMethod = new StringBuilder(afterApply[0].trim() + ")");
                int i = 1;
                while (i < afterApply.length && proveMethod.toString().replace("(", "").length() < proveMethod.toString().replace(")", "").length()) {
                    proveMethod.append(afterApply[i].trim()).append(")");
                    i++;
                }
                remainder = Arrays.stream(afterApply, i, afterApply.length).collect(Collectors.joining(")"));
            } else {
                afterApply = parts[1].trim().split("\\s", 2);
                proveMethod = new StringBuilder(afterApply[0].trim());
                remainder = afterApply.length > 1 ? afterApply[1].trim() : "";
            }

            lines.add(indexToAdd, "apply " + proveMethod);
            if (!remainder.isBlank()) {
                lines.add(indexToAdd + 1, remainder.trim());
            }
            return parts[0].trim();
        }

        for (String proofHelper : PROOF_HELPERS) {
            if (line.contains(proofHelper) && !line.startsWith(proofHelper) && !line.contains("proof")) {
                String[] parts = line.split(proofHelper, 2);
                lines.add(indexToAdd, proofHelper + " " + parts[1].trim());
                return parts[0].trim();
            }
        }

        if (line.contains("by") && !line.startsWith("by")) {
            String[] parts = line.split("by", 2);
            lines.add(indexToAdd, "by " + parts[1].trim());
            return parts[0].trim();
        } else if (Arrays.stream(LEMMA_STARTERS).anyMatch(line::startsWith) && line.contains("assumes")) {
            String[] parts = line.split("assumes", 2);
            lines.add(indexToAdd, "assumes " + parts[1].trim());
            return parts[0].trim();
        } else if (line.startsWith("assumes") && line.contains("shows")) {
            String[] parts = line.split("shows", 2);
            lines.add(indexToAdd, "shows " + parts[1].trim());
            return parts[0].trim();
        } else if (line.matches(".*[\\s)\"]and[\\s()\"].*")) {
            String[] parts = line.split("and", 2);
            if (parts.length > 1) {
                lines.add(indexToAdd, parts[1].trim());
            }
            return parts[0].trim() + " and";
        } else {
            return line;
        }
    }

    private static String removeMultipleProofHelpers(String line, List<String> cleanLines) {
        for (String proofHelper : PROOF_HELPERS) {
            if (line.indexOf(proofHelper) != line.lastIndexOf(proofHelper)) {
                String[] parts = line.split(proofHelper);
                StringBuilder newLine = new StringBuilder(parts[0] + proofHelper);
                for (int i = 1; i < parts.length; i++) {
                    newLine.append(" ").append(parts[i].trim());
                }

                line = newLine.toString();
            }

            if (!cleanLines.isEmpty() && line.startsWith(proofHelper) && cleanLines.getLast().startsWith(proofHelper) && cleanLines.getLast().length() + line.length() - proofHelper.length() < MAX_LINE_LENGTH) {
                cleanLines.set(cleanLines.size() - 1, cleanLines.getLast() + " " + line.substring(proofHelper.length()).trim());
                return "";
            }
        }

        return line;
    }

    private static String removeUnnecessaryBrackets(String line) {
        return line.replaceAll("\\(" + PROOVERS_REGEX + "([^\\s()',[0-9]]+)\\)", "$1");
    }

    private static String addAnds(String line, List<String> lines, int indexToAdd, List<String> cleanLines) {
        if (line.startsWith("assumes") || line.startsWith("shows") || line.startsWith("fixes")) {
            String[] parts = line.split("\"\\s\"|\"\"");

            if (parts.length == 1) {
                return line;
            }

            for (int i = 1; i < parts.length; i++) {
                String nextLine = "\"" + parts[i].trim() + (i < parts.length - 1 ? "\" and" : "");
                lines.add(indexToAdd + i - 1, nextLine);
            }
            return parts[0] + "\" and";
        } else if (line.startsWith("\"") && cleanLines.getLast().endsWith("\"")) {
            cleanLines.set(cleanLines.size() - 1, cleanLines.getLast() + " and");
            return line;
        } else {
            return line;
        }
    }

    private static String breakLongLines(String line, List<String> lines, int indexToAdd) {
        for (String proofHelper : PROOF_HELPERS) {
            if (line.startsWith(proofHelper) && line.length() > MAX_LINE_LENGTH) {
                String[] parts = line.split(" ");
                StringBuilder newLine = new StringBuilder(proofHelper);
                for (int i = 1; i < parts.length; i++) {
                    if (newLine.length() + parts[i].length() > MAX_LINE_LENGTH) {
                        lines.add(indexToAdd, proofHelper + " " + Arrays.stream(parts, i, parts.length).collect(Collectors.joining(" ")).trim());
                        return newLine.toString();
                    } else if (parts[i].contains("[")) {
                        int openBrackets = parts[i].chars().map(c -> c == '[' ? 1 : c == ']' ? -1 : 0).sum();
                        StringBuilder instantiation = new StringBuilder(parts[i]);
                        while (openBrackets > 0) {
                            i++;
                            openBrackets += parts[i].chars().map(c -> c == '[' ? 1 : c == ']' ? -1 : 0).sum();
                            instantiation.append(" ").append(parts[i]);
                        }
                        newLine.append(" ").append(instantiation);
                    } else {
                        newLine.append(" ").append(parts[i]);
                    }
                }
                return newLine.toString();
            }
        }
        return line;
    }

    private static String addApplyAutoBonk(String line) {
        if ((line.contains("apply auto") || line.contains("apply (auto")) && !line.contains("TODO")) {
            return line + " text \\<open> TODO: Fix! \\<close>";
        }
        return line;
    }

    private static boolean shouldUniteWithLastLine(String line, List<String> cleanLines) {
        if (cleanLines.isEmpty()) {
            return false;
        }

        String lastLine = cleanLines.getLast();
        return line.contains("proof") && lastLine.contains("show ");
    }

    private static void indentLines(List<String> cleanLines) {
        int currentIndentionLevel = 0;
        boolean insideQuotes = false;
        for (int i = 0; i < cleanLines.size(); i++) {
            String line = cleanLines.get(i);
            String previousLine = i > 0 ? cleanLines.get(i - 1) : "";

            int[] indentations = handleIndentionLevel(line, previousLine, currentIndentionLevel, insideQuotes);
            line = " ".repeat(indentations[0] * INDENTION_SIZE) + line.trim();
            currentIndentionLevel = indentations[1];
            cleanLines.set(i, line);

            long numberOfQuotesInLine = line.chars().filter(ch -> ch == '"').count();
            if (numberOfQuotesInLine % 2 == 1) {
                insideQuotes = !insideQuotes;
                if (!insideQuotes) {
                    squashUnnecessaryIndention(cleanLines, i);
                }
            }
        }
    }

    private static int[] handleIndentionLevel(String line, String previousLine, int currentIndentionLevel, boolean insideQuotes) {
        int[] indentationLevels;

        if (Stream.concat(Arrays.stream(LEMMA_STARTERS), Stream.concat(Arrays.stream(TEXT_STARTERS), Arrays.stream(OTHER_STARTERS))).anyMatch(line::startsWith)) {
            indentationLevels = new int[]{0, 0};
        } else if (Arrays.stream(COMMENT_STARTERS).anyMatch(line::startsWith)) {
            indentationLevels = new int[]{currentIndentionLevel, currentIndentionLevel};
        } else if (line.isBlank()) {
            indentationLevels = new int[]{0, currentIndentionLevel};
        } else if (line.startsWith("assumes") || line.startsWith("fixes") || line.startsWith("shows")) {
            if (line.endsWith("and")) {
                indentationLevels = new int[]{1, 2};
            } else {
                indentationLevels = new int[]{1, 1};
            }
        } else if (line.contains("proof")) {
            if (line.contains("show")) {
                indentationLevels = new int[]{currentIndentionLevel, currentIndentionLevel + 1};
            } else {
                indentationLevels = new int[]{0, 1};
            }
        } else if (line.startsWith("imports")) {
            indentationLevels = new int[]{1, 0};
        } else if (line.equals("qed")) {
            indentationLevels = new int[]{currentIndentionLevel - 1, currentIndentionLevel - 1};
        } else if (line.startsWith("by") || line.startsWith("apply") || Arrays.stream(PROOF_HELPERS).anyMatch(line::startsWith)) {
            indentationLevels = new int[]{currentIndentionLevel + 1, currentIndentionLevel};
        } else if (line.equals("next")) {
            indentationLevels = new int[]{currentIndentionLevel - 1, currentIndentionLevel};
        } else if (previousLine.contains("obtain")) {
            indentationLevels = new int[]{currentIndentionLevel + 1, currentIndentionLevel};
        } else if (!insideQuotes && Arrays.stream(STEP_STARTERS).anyMatch(line::startsWith)) {
            indentationLevels = new int[]{currentIndentionLevel, currentIndentionLevel};
        } else if (insideQuotes) {
            indentationLevels = new int[]{currentIndentionLevel + 1, currentIndentionLevel};
        } else {
            indentationLevels = new int[]{currentIndentionLevel, currentIndentionLevel};
        }

        int numberOfOpeningBrackets =
                line.length() - line.replaceAll("[(\\[]", "").length() + (line.length() - line.replaceAll("\\\\<lbrakk>", "").length()) / "\\<lbrakk>".length();
        int numberOfClosingBrackets = line.length() - line.replaceAll("[)\\]]", "").length() + (line.length() - line.replaceAll("\\\\<rbrakk>", "").length()) / "\\<rbrakk>".length();

        long numberOfQuotesInLine = line.chars().filter(ch -> ch == '"').count();
        if (numberOfQuotesInLine % 2 == 1) {
            if (insideQuotes) {
                numberOfClosingBrackets++;
            } else {
                numberOfOpeningBrackets++;
            }
        }

        indentationLevels[1] += numberOfOpeningBrackets - numberOfClosingBrackets;

        return indentationLevels;
    }

    private static void squashUnnecessaryIndention(List<String> cleanLines, int currentIndex) {
        List<String> linesToSquash = new ArrayList<>();
        linesToSquash.add(cleanLines.get(currentIndex));
        for (int i = currentIndex - 1; i >= 0; i--) {
            linesToSquash.addFirst(cleanLines.get(i));
            if (cleanLines.get(i).chars().filter(ch -> ch == '"').count() == 1) {
                break;
            }
        }
        List<Integer> indentionLevels = linesToSquash.stream()
                .map(line -> (line.length() - line.trim().length()) / INDENTION_SIZE)
                .distinct()
                .sorted()
                .toList();
        int baseIndention = indentionLevels.getFirst();
        for (int i = 0; i < linesToSquash.size(); i++) {
            String lineToSquash = linesToSquash.get(i);
            int indentionLevel = (lineToSquash.length() - lineToSquash.trim().length()) / INDENTION_SIZE;
            int indentationIndex = indentionLevels.indexOf(indentionLevel);
            int squashedIndentionLevel = (indentationIndex == 0 ? 0 : (indentationIndex + 1)) + baseIndention;
            cleanLines.set(currentIndex + i - linesToSquash.size() + 1, " ".repeat(squashedIndentionLevel * INDENTION_SIZE) + linesToSquash.get(i).trim());
        }
    }
}