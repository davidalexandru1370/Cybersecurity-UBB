package com.example.backend.core.exceptions;

public class ExistingAccountException extends Exception {
    public ExistingAccountException(String message) {
        super(message);
    }
}
