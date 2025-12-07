package com.example.backend.presentation.entities.response;

public class AuthResponse {
    private Boolean success;
    private String token;

    public AuthResponse(Boolean success, String token) {
        this.success = success;
        this.token = token;
    }
}
