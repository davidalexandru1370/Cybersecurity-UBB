package com.example.backend.presentation.entities.response;

public class AuthResponse {
    private Boolean success;
    private String token;
    private String refreshToken;

    public AuthResponse(Boolean success, String token, String refreshToken) {
        this.success = success;
        this.token = token;
        this.refreshToken = refreshToken;
    }

    public Boolean getSuccess() {
        return success;
    }

    public String getToken() {
        return token;
    }

    public String getRefreshToken() {
        return refreshToken;
    }
}
