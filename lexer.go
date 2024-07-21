package main

import (
	"fmt"
)

type Token struct {
	typetoken TokenType
	contents  string
	length    int
}

type Tokenizer struct {
	location string
	index    int
	count    int
}

type TokenType int

const (
	TokenType_IDENTIFIER TokenType = iota

	TokenType_NUM
	TokenType_OPERATOR
	TokenType_KEYWORD
	TokenType_CONSTANT

	TokenType_OTHER
	TokenType_EOF
	TokenType_ERROR
)

var TokenTypeStrings = map[TokenType]string{
	TokenType_IDENTIFIER: "TokenType_IDENTIFIER",
	TokenType_NUM:        "TokenType_NUM",
	TokenType_OPERATOR:   "TokenType_OPERATOR",
	TokenType_KEYWORD:    "TokenType_KEYWORD",
	TokenType_CONSTANT:   "TokenType_CONSTANT",
	TokenType_OTHER:      "TokenType_OTHER",
	TokenType_EOF:        "TokenType_EOF",
	TokenType_ERROR:      "TokenType_ERROR",
}

var size int

func isWhiteSpace(c byte) bool {
	res := (c == ' ') || (c == '\t') || (c == '\f') || (c == '\v')
	return res
}

func IsEndOfLine(c byte) bool {
	result := (c == '\n') || (c == '\r')
	return result
}

func IsLetter(c byte) bool {
	result := false

	if c >= 'A' && c <= 'Z' {
		result = true
	}
	if c >= 'a' && c <= 'z' {
		result = true
	}

	return result
}

func IsNumeric(c byte) bool {
	result := false

	if c >= '0' && c <= '9' {
		result = true
	}

	return result
}

func IgnoreCommentsAndWhiteSpace(tokenizer *Tokenizer) {
	if tokenizer.index != size && (IsEndOfLine(tokenizer.location[tokenizer.index]) || isWhiteSpace(tokenizer.location[tokenizer.index])) {
		tokenizer.index++
		for tokenizer.index != size && (IsEndOfLine(tokenizer.location[tokenizer.index]) || isWhiteSpace(tokenizer.location[tokenizer.index])) {
			tokenizer.index++
		}
	}
	// Look for $$ symbols for comments
	if tokenizer.index != size && (tokenizer.location[tokenizer.index] == '$') && (tokenizer.location[tokenizer.index+1] == '$') {
		for tokenizer.index != size && !IsEndOfLine(tokenizer.location[tokenizer.index]) {
			tokenizer.index++
		}
		tokenizer.index++
	}
}

func GetToken(tokenizer *Tokenizer) Token {
	token := Token{}
	token.length = 0
	IgnoreCommentsAndWhiteSpace(tokenizer)
	if tokenizer.index == size {
		token.typetoken = TokenType_EOF
		token.contents = "end_symbol"
		return token
	}
	switch tokenizer.location[tokenizer.index] {
	case '(':
		token.typetoken = TokenType_OTHER
		token.contents = "left_paren"
		tokenizer.index++
		token.length++
		break
	case ')':
		token.typetoken = TokenType_OTHER
		token.contents = "right_paren"
		tokenizer.index++
		token.length++
		break
	case '[':
		token.typetoken = TokenType_OTHER
		token.contents = "left_s_brac"
		tokenizer.index++
		token.length++
		break
	case ']':
		token.typetoken = TokenType_OTHER
		token.contents = "right_s_brac"
		tokenizer.index++
		token.length++
		break
	case '{':
		token.typetoken = TokenType_OTHER
		token.contents = "left_brac"
		tokenizer.index++
		token.length++
		break
	case '}':
		token.typetoken = TokenType_OTHER
		token.contents = "right_brac"
		tokenizer.index++
		token.length++
		break
	case ';':
		token.typetoken = TokenType_OTHER
		token.contents = "semicolon"
		tokenizer.index++
		token.length++
		break
	case '+':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '+' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "increment_by_one"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "addition"
		tokenizer.index++
		token.length++
		break
	case '-':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '-' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "decrement_by_one"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "subtraction"
		tokenizer.index++
		token.length++
		break
	case '*':
		token.typetoken = TokenType_OPERATOR
		token.contents = "multiplication"
		tokenizer.index++
		token.length++
		break
	case '/':
		token.typetoken = TokenType_OPERATOR
		token.contents = "division"
		tokenizer.index++
		token.length++
		break
	case '>':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '=' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "gth_equals_to"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "gth"
		tokenizer.index++
		token.length++
		break
	case '<':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '=' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "lth_equals_to"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "lth"
		tokenizer.index++
		token.length++
		break
	case '=':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '=' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "equals_to"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "assignment"
		tokenizer.index++
		token.length++
		break
	case '!':
		token.typetoken = TokenType_OPERATOR
		token.contents = "not"
		tokenizer.index++
		token.length++
		break
	case '~':
		token.typetoken = TokenType_OPERATOR
		token.contents = "bitwise_not"
		tokenizer.index++
		token.length++
		break
	case '&':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '&' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "and"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "bitwise_and"
		tokenizer.index++
		token.length++
		break
	case '|':
		if tokenizer.index != size-1 && tokenizer.location[tokenizer.index+1] == '|' {
			token.typetoken = TokenType_OPERATOR
			token.contents = "or"
			tokenizer.index += 2
			token.length += 2
			break
		}
		token.typetoken = TokenType_OPERATOR
		token.contents = "bitwise_or"
		tokenizer.index++
		token.length++
		break
	case '#':
		token.typetoken = TokenType_OPERATOR
		token.contents = "power"
		tokenizer.index++
		token.length++
		break
	case '^':
		token.typetoken = TokenType_OPERATOR
		token.contents = "xor"
		tokenizer.index++
		token.length++
		break
	case '%':
		token.typetoken = TokenType_OPERATOR
		token.contents = "modulo"
		tokenizer.index++
		token.length++
		break
	case ',':
		token.typetoken = TokenType_OTHER
		token.contents = "coma"
		tokenizer.index++
		token.length++
		break
	case '\'':
		// token.typetoken = TokenType_OTHER
		// token.contents = "quatation"
		// tokenizer.index++
		// token.length++
		// break
		token.typetoken = TokenType_CONSTANT
		var start_loc int = tokenizer.index
		tokenizer.index++
		var flag bool = false
		for tokenizer.index != size && tokenizer.location[tokenizer.index] != '\'' {
			tokenizer.index++
			token.length++
			if tokenizer.index == size {
				fmt.Println("You forgot to close the quotation mark")
				token.typetoken = TokenType_OTHER
				flag = true
				break
			}
		}
		if flag {
			token.contents = tokenizer.location[start_loc:tokenizer.index]
			break
		}
		tokenizer.index++
		token.contents = tokenizer.location[start_loc:tokenizer.index]
	case ':':
		token.typetoken = TokenType_OTHER
		token.contents = "colon"
		tokenizer.index++
		token.length++
		break
	case '"':
		token.typetoken = TokenType_CONSTANT
		var start_loc int = tokenizer.index
		tokenizer.index++
		var flag bool = false
		for tokenizer.index != size && tokenizer.location[tokenizer.index] != '"' {
			tokenizer.index++
			token.length++
			if tokenizer.index == size {
				fmt.Println("You forgot to close the quotation mark")
				token.typetoken = TokenType_OTHER
				flag = true
				break
			}
		}
		if flag {
			token.contents = tokenizer.location[start_loc:tokenizer.index]
			break
		}
		tokenizer.index++
		token.contents = tokenizer.location[start_loc:tokenizer.index]

	default:
		{
			if IsLetter(tokenizer.location[tokenizer.index]) {
				start_loc := tokenizer.index
				token.typetoken = TokenType_IDENTIFIER

				for tokenizer.index != size && (IsLetter(tokenizer.location[tokenizer.index]) || IsNumeric(tokenizer.location[tokenizer.index]) || tokenizer.location[tokenizer.index] == '_') {
					tokenizer.index++
					token.length++
				}

				token.contents = tokenizer.location[start_loc:tokenizer.index]
				if token.contents == "if" ||
					token.contents == "else_if" ||
					token.contents == "else" ||
					token.contents == "num" ||
					token.contents == "char" ||
					token.contents == "flag" ||
					token.contents == "str" ||
					token.contents == "void" ||
					token.contents == "true" ||
					token.contents == "false" ||
					token.contents == "len" ||
					token.contents == "headof" ||
					token.contents == "tailof" ||
					token.contents == "echo" ||
					token.contents == "floop" ||
					token.contents == "wloop" ||
					token.contents == "func" ||
					token.contents == "cons" ||
					token.contents == "cook" ||
					token.contents == "return" ||
					token.contents == "try" ||
					token.contents == "catch" ||
					token.contents == "throw" ||
					token.contents == "main" {
					token.typetoken = TokenType_KEYWORD
					break
				}
			} else if IsNumeric(tokenizer.location[tokenizer.index]) {
				start_loc := tokenizer.index
				token.typetoken = TokenType_NUM

				for tokenizer.index != size && IsNumeric(tokenizer.location[tokenizer.index]) {
					tokenizer.index++
					token.length++
				}
				token.contents = tokenizer.location[start_loc:tokenizer.index]
			} else {
				token.typetoken = TokenType_ERROR
				token.contents = string(tokenizer.location[tokenizer.index])
				tokenizer.index++
				token.length++
			}
		}

	}
	return token
}

func LexInput(input string) []Token {
	var tokenArray []Token
	tokenizer := Tokenizer{location: input, count: 0}
	lexing := true

	for lexing {
		token := GetToken(&tokenizer)

		tokenArray = append(tokenArray, token)

		if token.typetoken == TokenType_EOF {
			lexing = false
		} else if tokenizer.index == size {
			lexing = false
			var t Token
			t.typetoken = TokenType_EOF
			t.contents = "end_symbol"
			tokenArray = append(tokenArray, t)
		}
	}

	return tokenArray
}

// func LexFile(input string) {

// 	size = len(input)
// 	tokenarr := LexInput(input)
// 	return tokenarr

// }
